import Metal.S07_Capstone

/-!
# Solution — Stage 7: the fixed harness never crashes

Same shape as `Metal/S06_NoCrash.lean`. Read that first; the comments here
only point out what's different.
-/

namespace Metal.S07Solution
open Metal Reg Instr Machine

/-- Loop invariant at `.LBB0_4` (pc = 0x30). `i` is the *address offset*
    of the next byte to read (it starts at 1, not 0), and `e = 1 + n` is the
    offset of the end pointer. The facts `i < e` and `e ≤ len` are passed
    separately: they're what makes the `lbu` safe. -/
structure CapInv (len e i : Nat) (m : Machine) : Prop where
  pc : m.pc = 0x30
  a2 : m.reg a2 = inputBase + BitVec.ofNat 32 i
  a3 : m.reg a3 = inputBase + BitVec.ofNat 32 e
  ra : m.reg ra = 4
  rd : m.canRead = inInput len

theorem loop_iter (len e i : Nat) (m : Machine) (hlen : len < maxInput) (he : e ≤ len)
    (hi : i < e) (inv : CapInv len e i m) :
    ∃ m', run fixedProg 4 m = .running m' ∧
      (if i + 1 = e then m'.pc = 0x40 ∧ m'.reg ra = 4 else CapInv len e (i + 1) m') := by
  have hread := inInput_of_lt len i hlen (by omega)   -- needs i < len: from i < e ≤ len
  have hbne  := addr_succ_eq_iff i e (by omega) (by omega)
  by_cases h : i + 1 = e
  · sym [fixedProg, harness, inv.pc, inv.a2, inv.a3, inv.ra, inv.rd, hread, hbne, h]
  · sym [fixedProg, harness, inv.pc, inv.a2, inv.a3, inv.ra, inv.rd, hread, hbne, h]
    constructor <;> sym [inv.a3, inv.ra, inv.rd, addr_succ]

theorem loop_all (len e : Nat) (hlen : len < maxInput) (he : e ≤ len) :
    ∀ k i m, i + k = e → 0 < k → CapInv len e i m →
      ∃ m', run fixedProg (4 * k) m = .running m' ∧ m'.pc = 0x40 ∧ m'.reg ra = 4 := by
  intro k
  induction k with
  | zero => intro i m _ hk; omega
  | succ j ih =>
    intro i m hik _ inv
    obtain ⟨m1, h1, h1'⟩ := loop_iter len e i m hlen he (by omega) inv
    rw [show 4 * (j + 1) = 4 + 4 * j by omega, run_add_of_running _ _ _ _ _ h1]
    by_cases hj : j = 0
    · subst hj
      simp only [show i + 1 = e by omega, ite_true] at h1'
      exact ⟨m1, rfl, h1'⟩
    · simp only [show i + 1 ≠ e by omega, ite_false] at h1'
      exact ih (i + 1) m1 (by omega) (by omega) h1'

/-- From `.LBB0_5` (pc = 0x40): `ret`, `li a7 93`, `ecall`. -/
theorem exit_from_0x40 (m : Machine) (hpc : m.pc = 0x40) (hra : m.reg ra = 4) :
    ∃ c, run fixedProg 3 m = .halted c := by
  sym [fixedProg, harness, hpc, hra]

/-- The bounds facts about `n = data[0]` as a 32-bit value. -/
theorem n_facts (b : Byte) (len : Nat) (hlen : len < maxInput) :
    ((BitVec.setWidth 32 b).ult (BitVec.ofNat 32 len) = decide (b.toNat < len)) ∧
    ((BitVec.setWidth 32 b == 0#32) = decide (b.toNat = 0)) ∧
    (inputBase + 1#32 + BitVec.setWidth 32 b = inputBase + BitVec.ofNat 32 (1 + b.toNat)) := by
  simp only [maxInput, inputBase] at *
  have := b.isLt
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : b.toNat < len <;> simp [h, BitVec.ult] <;> bv_omega
  · by_cases h : b.toNat = 0 <;> simp [h] <;> bv_omega
  · bv_omega

theorem fixed_never_crashes : FixedSpec := by
  intro input hlen
  by_cases h0 : input.length = 0
  · -- size == 0: jal, beqz (taken), li, ret, li, ecall
    exact ⟨6, 0, by sym [fixedProg, harness, h0]⟩
  · have hne : BitVec.ofNat 32 input.length ≠ 0#32 := by
      simp only [maxInput] at hlen; bv_omega
    have hnil : input ≠ [] := by rintro rfl; simp at h0
    have hread0 : inInput input.length inputBase = true := by
      have := inInput_of_lt input.length 0 hlen (by omega); simpa using this
    -- n = data[0], as a byte; we never need to know its value, only its bounds
    obtain ⟨hult, hz, hend⟩ := n_facts ((load input).mem inputBase) input.length hlen
    by_cases hbig : ((load input).mem inputBase).toNat < input.length
    · by_cases hn0 : ((load input).mem inputBase).toNat = 0
      · -- n == 0: the beqz at 0x20 is taken → ret → exit
        exact ⟨10, 0, by sym [fixedProg, harness, hne, hnil, hread0, hult, hz, hbig, hn0]⟩
      · -- the interesting path: 1 ≤ n < size. Ten instructions to reach the loop.
        have : ∃ m, run fixedProg 10 (load input) = .running m ∧
            CapInv input.length (1 + ((load input).mem inputBase).toNat) 1 m := by
          sym [fixedProg, harness, hne, hnil, hread0, hult, hz, hbig, hn0, hend]
          constructor <;> sym
        obtain ⟨m, hrun, inv⟩ := this
        obtain ⟨m', hloop, hpc, hra⟩ :=
          loop_all input.length (1 + ((load input).mem inputBase).toNat) hlen (by omega)
            ((load input).mem inputBase).toNat 1 m (by omega) (by omega) inv
        obtain ⟨c, hc⟩ := exit_from_0x40 m' hpc hra
        refine ⟨10 + (4 * ((load input).mem inputBase).toNat + 3), c, ?_⟩
        rw [run_add_of_running _ _ _ _ _ hrun, run_add_of_running _ _ _ _ _ hloop]
        exact hc
    · -- n >= size: the bgeu at 0x1c rejects → ret → exit
      exact ⟨9, 0, by sym [fixedProg, harness, hne, hnil, hread0, hult, hbig]⟩

/-- info: 'Metal.S07Solution.fixed_never_crashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fixed_never_crashes

end Metal.S07Solution
