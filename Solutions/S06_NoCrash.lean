import Metal.S06_NoCrash

/-! # Solutions — Stage 6 -/

namespace Metal.S06Ex
open Metal Reg Instr Machine

/-! ## E6.1 ★★ `last_byte` is safe on every non-empty input -/

/-- `p + len - 1`, in the shape `simp` leaves it after `lbu a0, -1(a0)`. -/
theorem last_addr (len : Nat) (h1 : 1 ≤ len) (hlen : len < maxInput) :
    inputBase + BitVec.ofNat 32 len + 4294967295#32 = inputBase + BitVec.ofNat 32 (len - 1) := by
  simp only [inputBase, maxInput] at *; bv_omega

theorem e6_1 (input : List Byte) (hlen : input.length < maxInput) (hne : input ≠ []) :
    ExitsCleanly lastByteProg (load input) := by
  have h1 : 1 ≤ input.length := by
    cases input with
    | nil => contradiction
    | cons _ _ => simp
  have hread := inInput_of_lt input.length (input.length - 1) hlen (by omega)
  have haddr := last_addr input.length h1 hlen
  -- Checkpoint after `jal` and `add`: name the state and record what we know.
  -- (Going straight through all six steps from `load input` makes Lean's
  -- *kernel* re-derive register values by brute force — see docs/06 "When the
  -- kernel is slow". Checkpointing is also just good proof hygiene.)
  have : ∃ m, run lastByteProg 2 (load input) = .running m ∧ m.pc = 0x10 ∧
      m.reg a0 = inputBase + BitVec.ofNat 32 input.length ∧ m.reg ra = 4 ∧
      m.canRead = inInput input.length := by
    sym [lastByteProg]
  obtain ⟨m, hrun, hpc, ha0, hra, hrd⟩ := this
  -- `lbu a0, -1(a0)`, `ret`, `li a7, 93`, `ecall`
  have : ∃ c, run lastByteProg 4 m = .halted c := by
    sym [lastByteProg, hpc, ha0, hra, hrd, haddr, hread]
  obtain ⟨c, hc⟩ := this
  exact ⟨2 + 4, c, by rw [run_add_of_running _ _ _ _ _ hrun]; exact hc⟩

/-! ## E6.2 ★ …and violates the spec, because of the empty input -/
theorem e6_2 :
    ¬ ∀ input : List Byte, input.length < maxInput → ExitsCleanly lastByteProg (load input) := by
  intro h
  have hcrash : run lastByteProg 5 (load []) = .fault (.badRead 0xFFFF) := by rfl
  exact fault_final _ _ _ _ hcrash (h [] (by decide))

/-! ## E6.3 ★★ `count_zeros` never crashes -/

def czProg : Program := ⟨[
  /- 0x00 -/ jal ra 12,
  /- 0x04 -/ li a7 93,
  /- 0x08 -/ ecall,
  /- 0x0c -/ li a2 0,
  /- 0x10 -/ beqz a1 28,
  /- 0x14 -/ add a1 a0 a1,
  /- 0x18 -/ lbu a3 a0 0,
  /- 0x1c -/ seqz a3 a3,
  /- 0x20 -/ addi a0 a0 1,
  /- 0x24 -/ add a2 a2 a3,
  /- 0x28 -/ bne a0 a1 (-16),
  /- 0x2c -/ mv a0 a2,
  /- 0x30 -/ ret
]⟩

structure CzInv (len i : Nat) (m : Machine) : Prop where
  pc : m.pc = 0x18
  a0 : m.reg a0 = inputBase + BitVec.ofNat 32 i
  a1 : m.reg a1 = inputBase + BitVec.ofNat 32 len
  ra : m.reg ra = 4
  rd : m.canRead = inInput len

theorem cz_iter (len i : Nat) (m : Machine) (hlen : len < maxInput) (hi : i < len)
    (inv : CzInv len i m) :
    ∃ m', run czProg 5 m = .running m' ∧
      (if i + 1 = len then m'.pc = 0x2c ∧ m'.reg ra = 4 else CzInv len (i + 1) m') := by
  have hread := inInput_of_lt len i hlen hi
  have hbne  := addr_succ_eq_iff i len (by omega) hlen
  by_cases h : i + 1 = len
  · sym [czProg, inv.pc, inv.a0, inv.a1, inv.ra, inv.rd, hread, hbne, h]
  · sym [czProg, inv.pc, inv.a0, inv.a1, inv.ra, inv.rd, hread, hbne, h]
    constructor <;> sym [inv.a1, inv.ra, inv.rd, addr_succ]

theorem cz_loop (len : Nat) (hlen : len < maxInput) :
    ∀ k i m, i + k = len → 0 < k → CzInv len i m →
      ∃ m', run czProg (5 * k) m = .running m' ∧ m'.pc = 0x2c ∧ m'.reg ra = 4 := by
  intro k
  induction k with
  | zero => intro i m _ hk; omega
  | succ j ih =>
    intro i m hik _ inv
    obtain ⟨m1, h1, h1'⟩ := cz_iter len i m hlen (by omega) inv
    rw [show 5 * (j + 1) = 5 + 5 * j by omega, run_add_of_running _ _ _ _ _ h1]
    by_cases hj : j = 0
    · subst hj
      simp only [show i + 1 = len by omega, ite_true] at h1'
      exact ⟨m1, rfl, h1'⟩
    · simp only [show i + 1 ≠ len by omega, ite_false] at h1'
      exact ih (i + 1) m1 (by omega) (by omega) h1'

theorem cz_epilogue (m : Machine) (hpc : m.pc = 0x2c) (hra : m.reg ra = 4) :
    ∃ c, run czProg 4 m = .halted c := by
  sym [czProg, hpc, hra]

theorem e6_3 (input : List Byte) (hlen : input.length < maxInput) :
    ExitsCleanly czProg (load input) := by
  by_cases h0 : input.length = 0
  · exact ⟨7, 0, by sym [czProg, h0]⟩
  · have hne : BitVec.ofNat 32 input.length ≠ 0#32 := by
      simp only [maxInput] at hlen; bv_omega
    have : ∃ m, run czProg 4 (load input) = .running m ∧ CzInv input.length 0 m := by
      sym [czProg, hne]
      constructor <;> sym
    obtain ⟨m, hrun, inv⟩ := this
    obtain ⟨m', hloop, hpc, hra⟩ := cz_loop input.length hlen input.length 0 m (by omega) (by omega) inv
    obtain ⟨c, hc⟩ := cz_epilogue m' hpc hra
    refine ⟨4 + (5 * input.length + 4), c, ?_⟩
    rw [run_add_of_running _ _ _ _ _ hrun, run_add_of_running _ _ _ _ _ hloop]
    exact hc

/-! ## E6.4 ★★★ `max_byte`: a loop body with two paths -/

def mbProg : Program := ⟨[
  /- 0x00 -/ jal ra 12,
  /- 0x04 -/ li a7 93,
  /- 0x08 -/ ecall,
  /- 0x0c -/ li a2 0,
  /- 0x10 -/ beqz a1 36,
  /- 0x14 -/ add a1 a0 a1,
  /- 0x18 -/ j 12,
  /- 0x1c -/ addi a0 a0 1,
  /- 0x20 -/ beq a0 a1 20,
  /- 0x24 -/ lbu a3 a0 0,
  /- 0x28 -/ bltu a3 a2 (-12),
  /- 0x2c -/ mv a2 a3,
  /- 0x30 -/ j (-20),
  /- 0x34 -/ mv a0 a2,
  /- 0x38 -/ ret
]⟩

/-- The loop head is the `lbu` at 0x24. Same facts as before; nothing about
    `a2` (the running max), because safety doesn't depend on it. -/
structure MbInv (len i : Nat) (m : Machine) : Prop where
  pc : m.pc = 0x24
  a0 : m.reg a0 = inputBase + BitVec.ofNat 32 i
  a1 : m.reg a1 = inputBase + BitVec.ofNat 32 len
  ra : m.reg ra = 4
  rd : m.canRead = inInput len

/-- One iteration takes 4 steps (byte < max) or 6 (new max), so we say
    "some number of steps" instead of a fixed count. The proof splits on the
    one branch whose direction depends on the data. -/
theorem mb_iter (len i : Nat) (m : Machine) (hlen : len < maxInput) (hi : i < len)
    (inv : MbInv len i m) :
    ∃ n m', run mbProg n m = .running m' ∧
      (if i + 1 = len then m'.pc = 0x34 ∧ m'.reg ra = 4 else MbInv len (i + 1) m') := by
  have hread := inInput_of_lt len i hlen hi
  have hbeq  := addr_succ_eq_iff i len (by omega) hlen
  by_cases hb : (BitVec.setWidth 32 (m.mem (inputBase + BitVec.ofNat 32 i))).ult (m.reg a2) = true
  · -- byte < current max: lbu, bltu (taken), addi, beq
    refine ⟨4, ?_⟩
    by_cases h : i + 1 = len
    · sym [mbProg, inv.pc, inv.a0, inv.a1, inv.ra, inv.rd, hread, hbeq, hb, h]
    · sym [mbProg, inv.pc, inv.a0, inv.a1, inv.ra, inv.rd, hread, hbeq, hb, h]
      constructor <;> sym [inv.a1, inv.ra, inv.rd, addr_succ]
  · -- new max: lbu, bltu (not taken), mv, j, addi, beq
    refine ⟨6, ?_⟩
    by_cases h : i + 1 = len
    · sym [mbProg, inv.pc, inv.a0, inv.a1, inv.ra, inv.rd, hread, hbeq, hb, h]
    · sym [mbProg, inv.pc, inv.a0, inv.a1, inv.ra, inv.rd, hread, hbeq, hb, h]
      constructor <;> sym [inv.a1, inv.ra, inv.rd, addr_succ]

theorem mb_loop (len : Nat) (hlen : len < maxInput) :
    ∀ k i m, i + k = len → 0 < k → MbInv len i m →
      ∃ n m', run mbProg n m = .running m' ∧ m'.pc = 0x34 ∧ m'.reg ra = 4 := by
  intro k
  induction k with
  | zero => intro i m _ hk; omega
  | succ j ih =>
    intro i m hik _ inv
    obtain ⟨n1, m1, h1, h1'⟩ := mb_iter len i m hlen (by omega) inv
    by_cases hj : j = 0
    · subst hj
      simp only [show i + 1 = len by omega, ite_true] at h1'
      exact ⟨n1, m1, h1, h1'⟩
    · simp only [show i + 1 ≠ len by omega, ite_false] at h1'
      obtain ⟨n2, m2, h2, h2'⟩ := ih (i + 1) m1 (by omega) (by omega) h1'
      exact ⟨n1 + n2, m2, by rw [run_add_of_running _ _ _ _ _ h1]; exact h2, h2'⟩

theorem e6_4 (input : List Byte) (hlen : input.length < maxInput) :
    ExitsCleanly mbProg (load input) := by
  by_cases h0 : input.length = 0
  · exact ⟨7, 0, by sym [mbProg, h0]⟩
  · have hne : BitVec.ofNat 32 input.length ≠ 0#32 := by
      simp only [maxInput] at hlen; bv_omega
    have : ∃ m, run mbProg 5 (load input) = .running m ∧ MbInv input.length 0 m := by
      sym [mbProg, hne]
      constructor <;> sym
    obtain ⟨m, hrun, inv⟩ := this
    obtain ⟨n, m', hloop, hpc, hra⟩ := mb_loop input.length hlen input.length 0 m (by omega) (by omega) inv
    have hexit : ∃ c, run mbProg 4 m' = .halted c := by sym [mbProg, hpc, hra]
    obtain ⟨c, hc⟩ := hexit
    refine ⟨5 + (n + 4), c, ?_⟩
    rw [run_add_of_running _ _ _ _ _ hrun, run_add_of_running _ _ _ _ _ hloop]
    exact hc

end Metal.S06Ex
