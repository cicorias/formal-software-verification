import Metal.S07_Capstone

/-!
# Exercises — Stage 7: prove the fixed harness never crashes

This is the capstone: the article's job, start to finish, on one function.
`Metal/S07_Capstone.lean` has the programs, the bug, and the statement
`FixedSpec`. You prove it.

Roadmap (each step is a `sorry` below):
1. `loop_iter`   one trip around the loop at 0x30 (4 instructions).
2. `loop_all`    induction on the iterations left (copy Stage 6's shape).
3. `exit_from_0x40`  `ret`, `li a7 93`, `ecall`.
4. `n_facts`     three facts about n = data[0] as a 32-bit value.
5. `fixed_never_crashes`  four paths through the prologue:
   * size == 0                    → exits (6 steps)
   * n ≥ size  (the fixed check)  → exits (9 steps)
   * n == 0                       → exits (10 steps)
   * 1 ≤ n < size                 → 10 steps to the loop, the loop, 3 to exit.

Count steps with `trace fixedProg [...]` on a concrete input if you're unsure.

Then the reflection question, as a comment at the bottom: where exactly does
this proof break if you try it on `buggyProg`? Which hypothesis can't you
establish?

Check: `lake build Exercises.S07_Capstone`.
-/

namespace Metal.S07Ex
open Metal Reg Instr Machine

/-- Loop invariant at `.LBB0_4` (pc = 0x30). `i` is the address offset of
    the next byte (it starts at 1), `e = 1 + n` the offset of the end. -/
structure CapInv (len e i : Nat) (m : Machine) : Prop where
  pc : m.pc = 0x30
  a2 : m.reg a2 = inputBase + BitVec.ofNat 32 i
  a3 : m.reg a3 = inputBase + BitVec.ofNat 32 e
  ra : m.reg ra = 4
  rd : m.canRead = inInput len

/-- Hint: exactly like `Metal.loop_iter` in S06_NoCrash.lean. You need `i < len`
    for the read to be safe; you have `i < e` and `e ≤ len`. -/
theorem loop_iter (len e i : Nat) (m : Machine) (hlen : len < maxInput) (he : e ≤ len)
    (hi : i < e) (inv : CapInv len e i m) :
    ∃ m', run fixedProg 4 m = .running m' ∧
      (if i + 1 = e then m'.pc = 0x40 ∧ m'.reg ra = 4 else CapInv len e (i + 1) m') := by
  sorry

theorem loop_all (len e : Nat) (hlen : len < maxInput) (he : e ≤ len) :
    ∀ k i m, i + k = e → 0 < k → CapInv len e i m →
      ∃ m', run fixedProg (4 * k) m = .running m' ∧ m'.pc = 0x40 ∧ m'.reg ra = 4 := by
  sorry

theorem exit_from_0x40 (m : Machine) (hpc : m.pc = 0x40) (hra : m.reg ra = 4) :
    ∃ c, run fixedProg 3 m = .halted c := by
  sorry

/-- The prologue compares `zext(n)` with `size` (unsigned), tests `n == 0`, and
    computes `end = data + 1 + n`. State those three facts in the shapes `sym`
    will need them. Hints: `b.isLt : b.toNat < 2^8`; case-split with
    `by_cases`, then `simp [h, BitVec.ult]` and `bv_omega`. -/
theorem n_facts (b : Byte) (len : Nat) (hlen : len < maxInput) :
    ((BitVec.setWidth 32 b).ult (BitVec.ofNat 32 len) = decide (b.toNat < len)) ∧
    ((BitVec.setWidth 32 b == 0#32) = decide (b.toNat = 0)) ∧
    (inputBase + 1#32 + BitVec.setWidth 32 b = inputBase + BitVec.ofNat 32 (1 + b.toNat)) := by
  sorry

/-- The capstone. Hints:
* You'll need `input ≠ []` and `BitVec.ofNat 32 input.length ≠ 0#32` for the
  non-empty case (simp turns `ofNat len == 0` into `input = []`).
* `inInput input.length inputBase = true` (from `inInput_of_lt` at 0).
* Don't try to learn the value of `n`: work with the byte
  `(load input).mem inputBase` symbolically, and case-split on
  `((load input).mem inputBase).toNat < input.length` and `… = 0`.
* When `sym` leaves `0#32 = ?m`, give the exit code explicitly. -/
theorem fixed_never_crashes : FixedSpec := by
  sorry

/-
Reflection: where does the proof break for `buggyProg`?
(Write your answer here.)
-/

end Metal.S07Ex
