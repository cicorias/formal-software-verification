import Metal.S06_NoCrash

/-!
# Exercises — Stage 6: no-crash proofs

Model every proof on `Metal/S06_NoCrash.lean`. The pattern is always:
1. **Prologue**: `sym` from `load input` to the loop head; establish the invariant.
2. **One iteration**: from the invariant at `i`, `sym` around the loop once.
   Feed `sym` the facts it needs: the pc, the registers, and the bounds
   facts (`inInput_of_lt`, `addr_succ_eq_iff`).
3. **All iterations**: induction on the number of iterations left.
4. **Epilogue**: `sym` from the exit label to `ecall`.
5. **Glue**: `run_add_of_running` to chain the pieces.

When `sym` leaves a goal, *read it*. It's either a fact you forgot to pass
in, or a fact you need to prove first (usually with `bv_omega`).

Check: `lake build Exercises.S06_NoCrash`.
-/

namespace Metal.S06Ex
open Metal Reg Instr Machine

/-! ## E6.1 ★★ `last_byte` is safe on non-empty inputs (no loop!)
The `lbu a0, -1(a0)` reads address `data + len + 0xFFFFFFFF` (that's `-1`
sign-extended). First prove that's `data + (len - 1)`, then that it's
readable, then `sym` through.

Important: checkpoint after the first two instructions (state the facts about
the machine at pc 0x10 as an `∃ m, ...` and `obtain` it), then `sym` the
remaining four from that abstract `m`. See docs/06 "When the kernel is slow"
for why going straight through can make Lean's kernel take forever. -/

theorem last_addr (len : Nat) (h1 : 1 ≤ len) (hlen : len < maxInput) :
    inputBase + BitVec.ofNat 32 len + 4294967295#32 = inputBase + BitVec.ofNat 32 (len - 1) := by
  sorry

theorem e6_1 (input : List Byte) (hlen : input.length < maxInput) (hne : input ≠ []) :
    ExitsCleanly lastByteProg (load input) := by
  sorry

/-! ## E6.2 ★ …but `last_byte` fails the spec.
Use `fault_final` (S06_SymExec) with a concrete crashing run. -/
theorem e6_2 :
    ¬ ∀ input : List Byte, input.length < maxInput → ExitsCleanly lastByteProg (load input) := by
  sorry

/-! ## E6.3 ★★ `count_zeros` never crashes
Here is the (correct) transcription, and the loop invariant. The loop body
is five instructions now (`seqz` is new), so one iteration is `run czProg 5`. -/

def czProg : Program := ⟨[
  /- 0x00 -/ jal ra 12,
  /- 0x04 -/ li a7 93,
  /- 0x08 -/ ecall,
  /- 0x0c -/ li a2 0,
  /- 0x10 -/ beqz a1 28,         -- → 0x2c
  /- 0x14 -/ add a1 a0 a1,
  /- 0x18 -/ lbu a3 a0 0,        -- loop head
  /- 0x1c -/ seqz a3 a3,
  /- 0x20 -/ addi a0 a0 1,
  /- 0x24 -/ add a2 a2 a3,
  /- 0x28 -/ bne a0 a1 (-16),    -- → 0x18
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
  sorry

theorem cz_loop (len : Nat) (hlen : len < maxInput) :
    ∀ k i m, i + k = len → 0 < k → CzInv len i m →
      ∃ m', run czProg (5 * k) m = .running m' ∧ m'.pc = 0x2c ∧ m'.reg ra = 4 := by
  sorry

theorem cz_epilogue (m : Machine) (hpc : m.pc = 0x2c) (hra : m.reg ra = 4) :
    ∃ c, run czProg 4 m = .halted c := by
  sorry

theorem e6_3 (input : List Byte) (hlen : input.length < maxInput) :
    ExitsCleanly czProg (load input) := by
  sorry

/-! ## E6.4 ★★★ `max_byte`: write your own invariant
The loop body has a data-dependent branch, so one iteration takes 4 *or* 6
steps. That means you can't say `run mbProg 4 m`; say `∃ n m', run mbProg n m
= .running m' ∧ ...` instead, and glue iterations with `n₁ + n₂`.
Choose the loop head (hint: the `lbu`), write the invariant, and prove it.
In the iteration lemma, case-split on the one branch condition whose value
you can't know: `by_cases hb : (BitVec.setWidth 32 (m.mem (inputBase + BitVec.ofNat 32 i))).ult (m.reg a2) = true`. -/

def mbProg : Program := ⟨[
  /- 0x00 -/ jal ra 12,
  /- 0x04 -/ li a7 93,
  /- 0x08 -/ ecall,
  /- 0x0c -/ li a2 0,
  /- 0x10 -/ beqz a1 36,         -- → 0x34
  /- 0x14 -/ add a1 a0 a1,
  /- 0x18 -/ j 12,               -- → 0x24
  /- 0x1c -/ addi a0 a0 1,
  /- 0x20 -/ beq a0 a1 20,       -- → 0x34
  /- 0x24 -/ lbu a3 a0 0,
  /- 0x28 -/ bltu a3 a2 (-12),   -- → 0x1c
  /- 0x2c -/ mv a2 a3,
  /- 0x30 -/ j (-20),            -- → 0x1c
  /- 0x34 -/ mv a0 a2,
  /- 0x38 -/ ret
]⟩

theorem e6_4 (input : List Byte) (hlen : input.length < maxInput) :
    ExitsCleanly mbProg (load input) := by
  sorry

end Metal.S06Ex
