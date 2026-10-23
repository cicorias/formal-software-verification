import Metal.S06_SymExec
import Metal.S05_Playground

/-!
# Stage 6b — Proving a compiled loop never crashes, for *every* input

This is the article's method in miniature:

    C source  ──clang -O1 --target=riscv32──▶  RISC-V assembly  ──transcribe──▶  `sumProg`
    "this harness never crashes on inputs < 64 MiB"  ──▶  `sum_exits_cleanly`  (a theorem)

The C (see `c/sum.c`):

```c
uint32_t sum(const uint8_t *p, uint32_t len) {
  uint32_t s = 0;
  for (uint32_t i = 0; i < len; i++) s += p[i];
  return s;
}
```

`clang --target=riscv32-unknown-elf -march=rv32i -O1 -S` produced the body
below, *verbatim* (only the addresses and the `_start` stub are ours). Notice
that clang turned `i < len` into "pointer != end pointer". A source-level proof
would never see that, and that is the gap the article closes by proving facts
about binaries. Our theorem is about what the CPU actually runs.

Read `docs/06-no-crash.md` first: it explains the proof's shape (prologue,
loop invariant, epilogue) before you read the Lean.
-/

namespace Metal
open Reg Instr Machine

/-- The program. `_start` calls `sum(data, size)` and then `exit(result)`. -/
def sumProg : Program := ⟨[
  /- 0x00 _start: -/ jal ra 12,          -- call sum            (→ 0x0c)
  /- 0x04 -/         li a7 93,           -- a7 = SYS_exit
  /- 0x08 -/         ecall,              -- exit(a0)
  /- 0x0c sum:    -/ li a2 0,            -- s = 0
  /- 0x10 -/         beqz a1 24,         -- if len == 0 goto .done (→ 0x28)
  /- 0x14 -/         add a1 a0 a1,       -- end = p + len
  /- 0x18 .loop:  -/ lbu a3 a0 0,        -- t = *p          ← the only memory access
  /- 0x1c -/         addi a0 a0 1,       -- p++
  /- 0x20 -/         add a2 a2 a3,       -- s += t
  /- 0x24 -/         bne a0 a1 (-12),    -- if p != end goto .loop (→ 0x18)
  /- 0x28 .done:  -/ mv a0 a2,           -- return s
  /- 0x2c -/         ret
]⟩

/-! ## Step 0: run it. A theorem prover is also a test harness. -/

#eval (run sumProg 1000 (load [1, 2, 3, 250])).show   -- exit(256)
#eval (run sumProg 1000 (load [])).show               -- exit(0)

/-- A *test*, checked by the kernel: one concrete input. `rfl` means "just
    compute both sides and compare". This is what a fuzzer does, once. -/
example : ExitsWith sumProg (load [1, 2, 3]) 6 := ⟨100, rfl⟩

/-! ## Step 1: the loop invariant

At the top of the loop (pc = 0x18), after `i` iterations, what is true?
This is the same thing you'd write in a comment above a C loop, except the
prover will hold us to every word of it.

Note what is *not* here: nothing about `a2` (the running sum) or `a3`.
For "doesn't crash" we don't care what the sum is. Stage 8 shows why that
should make you nervous. -/
structure LoopInv (len i : Nat) (m : Machine) : Prop where
  pc : m.pc = 0x18                                  -- we're at .loop
  a0 : m.reg a0 = inputBase + BitVec.ofNat 32 i     -- p   = data + i
  a1 : m.reg a1 = inputBase + BitVec.ofNat 32 len   -- end = data + len
  ra : m.reg ra = 4                                 -- return address intact
  rd : m.canRead = inInput len                      -- shadow map unchanged

/-! ## Step 2: one trip around the loop

From the invariant at `i` (with `i < len`), four instructions later we are
either back at the top with the invariant at `i+1`, or (when `i+1 = len`) at
`.done` with the return address intact. -/
theorem loop_iter (len i : Nat) (m : Machine) (hlen : len < maxInput) (hi : i < len)
    (inv : LoopInv len i m) :
    ∃ m', run sumProg 4 m = .running m' ∧
      (if i + 1 = len then m'.pc = 0x28 ∧ m'.reg ra = 4 else LoopInv len (i + 1) m') := by
  -- The two facts symbolic execution will need:
  have hread := inInput_of_lt len i hlen hi              -- the lbu is in bounds
  have hbne  := addr_succ_eq_iff i len (by omega) hlen   -- when does p+1 == end?
  by_cases h : i + 1 = len
  · -- last iteration: the bne falls through to .done
    sym [sumProg, inv.pc, inv.a0, inv.a1, inv.ra, inv.rd, hread, hbne, h]
  · -- not last: the bne jumps back to .loop
    sym [sumProg, inv.pc, inv.a0, inv.a1, inv.ra, inv.rd, hread, hbne, h]
    constructor <;> sym [inv.a1, inv.ra, inv.rd, addr_succ]

/-! ## Step 3: the whole loop, by induction on the iterations left

`k` = number of iterations remaining = `len - i`. This is the *variant*: it
goes down by one each time around, which is why the loop terminates. In C
terms: the invariant says the loop is safe, the variant says it ends. -/
theorem loop_all (len : Nat) (hlen : len < maxInput) :
    ∀ k i m, i + k = len → 0 < k → LoopInv len i m →
      ∃ m', run sumProg (4 * k) m = .running m' ∧ m'.pc = 0x28 ∧ m'.reg ra = 4 := by
  intro k
  induction k with
  | zero => intro i m _ hk; omega
  | succ j ih =>
    intro i m hik _ inv
    obtain ⟨m1, h1, h1'⟩ := loop_iter len i m hlen (by omega) inv
    rw [show 4 * (j + 1) = 4 + 4 * j by omega, run_add_of_running _ _ _ _ _ h1]
    by_cases hj : j = 0
    · -- that was the last iteration
      subst hj
      simp only [show i + 1 = len by omega, ite_true] at h1'
      exact ⟨m1, rfl, h1'⟩
    · -- more to go: use the induction hypothesis from i+1
      simp only [show i + 1 ≠ len by omega, ite_false] at h1'
      exact ih (i + 1) m1 (by omega) (by omega) h1'

/-! ## Step 4: the epilogue — `mv`, `ret`, `li a7 93`, `ecall` -/
theorem epilogue (m : Machine) (hpc : m.pc = 0x28) (hra : m.reg ra = 4) :
    ∃ c, run sumProg 4 m = .halted c := by
  sym [sumProg, hpc, hra]

/-! ## Step 5: the theorem

For **every** input shorter than 64 MiB, the program exits without faulting.
That is 256^0 + 256^1 + … + 256^(64 MiB − 1) inputs. No fuzzer will ever
enumerate them; this proof covers all of them, and Lean checks it in about
a second. -/
theorem sum_exits_cleanly (input : List Byte) (hlen : input.length < maxInput) :
    ExitsCleanly sumProg (load input) := by
  by_cases h0 : input.length = 0
  · -- Empty input: jal, li, beqz (taken) → .done; then the epilogue.
    have : ∃ m, run sumProg 3 (load input) = .running m ∧ m.pc = 0x28 ∧ m.reg ra = 4 := by
      sym [sumProg, h0]
    obtain ⟨m, hrun, hpc, hra⟩ := this
    obtain ⟨c, hc⟩ := epilogue m hpc hra
    exact ⟨3 + 4, c, by rw [run_add_of_running _ _ _ _ _ hrun]; exact hc⟩
  · -- Non-empty: jal, li, beqz (not taken), add → top of loop with i = 0.
    have hne : BitVec.ofNat 32 input.length ≠ 0#32 := by
      simp only [maxInput] at hlen; bv_omega
    have : ∃ m, run sumProg 4 (load input) = .running m ∧ LoopInv input.length 0 m := by
      sym [sumProg, hne]
      constructor <;> sym
    obtain ⟨m, hrun, inv⟩ := this
    obtain ⟨m', hloop, hpc, hra⟩ :=
      loop_all input.length hlen input.length 0 m (by omega) (by omega) inv
    obtain ⟨c, hc⟩ := epilogue m' hpc hra
    refine ⟨4 + 4 * input.length + 4, c, ?_⟩
    rw [Nat.add_assoc, run_add_of_running _ _ _ _ _ hrun, run_add_of_running _ _ _ _ _ hloop]
    exact hc

/-- The final statement, in the exact shape the article uses: a property of a
    binary, quantified over all inputs below a size bound. -/
theorem sum_never_crashes :
    ∀ input : List Byte, input.length < maxInput → ExitsCleanly sumProg (load input) :=
  sum_exits_cleanly

-- What did that proof rely on? Only Lean's three standard axioms.
/-- info: 'Metal.sum_never_crashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sum_never_crashes

end Metal
