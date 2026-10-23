import Metal.S08_Trust
import Solutions.S07_Capstone

/-! # Solutions — Stage 8 -/

namespace Metal.S08Ex
open Metal Metal.Trust Reg Instr Machine

/-! ## E8.1 Audit an agent's claims -/

/-- (a) The agent's claim. -/
theorem claim_a : ∀ input : List Byte, input.length < maxInput → input.length > maxInput + 5 →
    ExitsCleanly buggyProg (load input) := by
  intro input h1 h2; omega

/-- Why it's worthless: no input satisfies the hypotheses. -/
theorem e8_1a : ¬ ∃ input : List Byte, input.length < maxInput ∧ input.length > maxInput + 5 := by
  intro ⟨_, h1, h2⟩; omega

/-- (b) A program that crashes on its first instruction (reads address 0). -/
def crashProg : Program := ⟨[lbu a0 zero 0, li a7 93, ecall]⟩

theorem e8_1b_weak : NoFaultWithin crashProg (load []) := everything_is_safe _ _

theorem e8_1b_real : ¬ ExitsCleanly crashProg (load []) := by
  have h : run crashProg 1 (load []) = .fault (.badRead 0) := by rfl
  exact fault_final _ _ _ _ h

/-- (c) The agent "fixed" the harness by making the length check always
    reject (`bgeu x0, x0` is always taken). It never crashes… -/
def agentProg : Program := harness (bgeu zero zero 36)

/-- …and it never does anything. On `[1, 5]` the real fix sums the payload (5);
    the agent's version returns 0. -/
theorem e8_1c : exitCode fixedProg [1, 5] ≠ exitCode agentProg [1, 5] := by
  decide

/-- The same, with the actual values: 5 versus 0. -/
example : exitCode fixedProg [1, 5] = some 5 ∧ exitCode agentProg [1, 5] = some 0 := by
  decide

/-- (d) `#print axioms` on the agent's theorem shows an axiom that isn't one
    of the three standard ones. Reject. (Answer as a comment in the exercise.) -/
axiom agent_lemma : ∀ input : List Byte, ExitsCleanly buggyProg (load input)
theorem claim_d : ∀ input : List Byte, input.length < maxInput → ExitsCleanly buggyProg (load input) :=
  fun input _ => agent_lemma input
-- #print axioms claim_d   -- [agent_lemma]  ← that's the problem

/-! ## E8.2 ★★★ Functional correctness of the capstone harness -/

/-- The reference: what the harness *should* return. -/
def capResult (input : List Byte) : Word :=
  match input with
  | []        => 0
  | n :: rest => if n.toNat < input.length then checksum (rest.take n.toNat) else 0

example : exitCode fixedProg [2, 10, 20] = some 30 := by rfl
example : capResult [2, 10, 20] = 30 := by rfl

/-- Invariant at 0x30, after `j` payload bytes: the pointer is at offset
    `j + 1` (just past the length byte), and `a0` holds the checksum of the
    first `j` payload bytes. Everything is stated in the forms `simp` produces
    (`input.tail`, `j + 1`), so that `sym` can use these facts as rewrites. -/
structure CapFunInv (input : List Byte) (n j : Nat) (m : Machine) : Prop where
  pc  : m.pc = 0x30
  a2  : m.reg a2 = inputBase + BitVec.ofNat 32 (j + 1)
  a3  : m.reg a3 = inputBase + BitVec.ofNat 32 (n + 1)
  a0  : m.reg a0 = checksum (input.tail.take j)
  ra  : m.reg ra = 4
  rd  : m.canRead = inInput input.length
  mem : m.mem = (load input).mem

theorem cap_iter (input : List Byte) (n j : Nat) (m : Machine) (hlen : input.length < maxInput)
    (hn : n + 1 ≤ input.length) (hj : j < n) (inv : CapFunInv input n j m) :
    ∃ m', run fixedProg 4 m = .running m' ∧
      (if j + 1 = n then m'.pc = 0x40 ∧ m'.reg ra = 4 ∧ m'.reg a0 = checksum (input.tail.take n)
       else CapFunInv input n (j + 1) m') := by
  have hread := inInput_of_lt input.length (j + 1) hlen (by omega)
  have hbne  := addr_succ_eq_iff (j + 1) (n + 1) (by omega) (by omega)
  have hbyte := load_mem input (j + 1) hlen (by omega)
  have hsum  := checksum_take_succ input.tail j (by simp; omega)
  by_cases h : j + 1 = n
  · subst h
    sym [fixedProg, harness, inv.pc, inv.a2, inv.a3, inv.a0, inv.ra, inv.rd, inv.mem,
      hread, hbne, hbyte, hsum]
  · sym [fixedProg, harness, inv.pc, inv.a2, inv.a3, inv.a0, inv.ra, inv.rd, inv.mem,
      hread, hbne, hbyte, h]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      sym [inv.a3, inv.ra, inv.rd, inv.mem, addr_succ, hsum]

theorem cap_loop (input : List Byte) (n : Nat) (hlen : input.length < maxInput)
    (hn : n + 1 ≤ input.length) :
    ∀ k j m, j + k = n → 0 < k → CapFunInv input n j m →
      ∃ m', run fixedProg (4 * k) m = .running m' ∧
        m'.pc = 0x40 ∧ m'.reg ra = 4 ∧ m'.reg a0 = checksum (input.tail.take n) := by
  intro k
  induction k with
  | zero => intro j m _ hk; omega
  | succ k ih =>
    intro j m hjk _ inv
    obtain ⟨m1, h1, h1'⟩ := cap_iter input n j m hlen hn (by omega) inv
    rw [show 4 * (k + 1) = 4 + 4 * k by omega, run_add_of_running _ _ _ _ _ h1]
    by_cases hk : k = 0
    · subst hk
      simp only [show j + 1 = n by omega, ite_true] at h1'
      exact ⟨m1, rfl, h1'⟩
    · simp only [show j + 1 ≠ n by omega, ite_false] at h1'
      exact ih (j + 1) m1 (by omega) (by omega) h1'

theorem e8_2 (input : List Byte) (hlen : input.length < maxInput) :
    ExitsWith fixedProg (load input) (capResult input) := by
  match input, hlen with
  | [], _ => exact ⟨6, rfl⟩
  | b :: rest, hlen =>
    -- Make the input opaque, so `simp` can't rewrite `(b :: rest).length`
    -- into a shape our hypotheses no longer match.
    generalize hin : b :: rest = input at hlen ⊢
    have hres : capResult input =
        if b.toNat < input.length then checksum (input.tail.take b.toNat) else 0 := by
      subst hin; rfl
    have hne : BitVec.ofNat 32 input.length ≠ 0#32 := by
      subst hin; simp only [maxInput, List.length_cons] at hlen ⊢; bv_omega
    have hnil : input ≠ [] := by subst hin; simp
    have hread0 : inInput input.length inputBase = true := by
      have := inInput_of_lt input.length 0 hlen (by subst hin; simp); simpa using this
    have hb : (load input).mem inputBase = b := by
      have := load_mem input 0 hlen (by subst hin; simp); subst hin; simpa using this
    -- Facts about n = data[0], stated for the byte `b`:
    obtain ⟨hult, hz, hend⟩ := Metal.S07Solution.n_facts b input.length hlen
    have hend' : inputBase + 1#32 + BitVec.setWidth 32 b = inputBase + BitVec.ofNat 32 (b.toNat + 1) := by
      rw [hend]; congr 1; congr 1; omega
    rw [hres]
    by_cases hbig : b.toNat < input.length
    · simp only [hbig, ite_true]
      by_cases hn0 : b.toNat = 0
      · -- n == 0: early exit with sum 0 = checksum []
        refine ⟨10, ?_⟩
        sym [fixedProg, harness, hne, hnil, hread0, hb, hult, hz, hbig, hn0, checksum]
      · have : ∃ m, run fixedProg 10 (load input) = .running m ∧ CapFunInv input b.toNat 0 m := by
          sym [fixedProg, harness, hne, hnil, hread0, hb, hult, hz, hbig, hn0, hend']
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sym [checksum]
        obtain ⟨m, hrun, inv⟩ := this
        obtain ⟨m', hloop, hpc, hra, ha0⟩ :=
          cap_loop input b.toNat hlen (by omega) b.toNat 0 m (by omega) (by omega) inv
        refine ⟨10 + (4 * b.toNat + 3), ?_⟩
        rw [run_add_of_running _ _ _ _ _ hrun, run_add_of_running _ _ _ _ _ hloop]
        sym [fixedProg, harness, hpc, hra, ha0]
    · simp only [hbig, ite_false]
      exact ⟨9, by sym [fixedProg, harness, hne, hnil, hread0, hb, hult, hbig]⟩

/-- info: 'Metal.S08Ex.e8_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms e8_2

end Metal.S08Ex
