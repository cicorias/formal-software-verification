import Metal.S06_NoCrash

/-!
# Stage 7 — Capstone: a fuzz harness, a bug, a fix, a proof

This is the article's loop, end to end, on a program small enough to hold in
your head:

1. A C fuzz harness (`c/harness_buggy.c`) parses a length-prefixed record.
2. clang compiles it to RISC-V. We transcribe the assembly instruction for
   instruction (`buggyProg`).
3. We state the spec: *for every input < 64 MiB, the harness exits cleanly.*
4. Trying to prove it fails — at exactly the instruction that reads out of
   bounds. The failed proof obligation *is* the bug report.
5. We **prove the negation** for the buggy binary: a machine-checked
   counterexample.
6. One-instruction fix (`fixedProg`), and the proof goes through
   (`Solutions/S07_Capstone.lean`; your job in `Exercises/S07_Capstone.lean`).

```c
// Record format: [n][payload: n bytes]. Sum the payload.
uint32_t LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  if (size == 0) return 0;
  size_t n = data[0];
  if (n > size) return 0;           // BUG: payload starts at data[1], so need n <= size-1
  uint32_t s = 0;
  for (size_t i = 0; i < n; i++) s += data[1 + i];
  return s;
}
```

clang's output for the buggy and fixed versions differs in **one instruction**
(at 0x1c below): `bltu a1, a3` ("if size < n, reject") versus `bgeu a3, a1`
("if n ≥ size, reject"). Both were produced by
`clang --target=riscv32-unknown-elf -march=rv32i -mabi=ilp32 -O1 -S`.

(One liberty: a real OSS-Fuzz harness must `return 0`. We return the sum so
clang keeps the loop, and so Stage 8 has something to check.)
-/

namespace Metal
open Reg Instr Machine

/-- The harness body; `reject` is the instruction at 0x1c that differs. -/
def harness (reject : Instr) : Program := ⟨[
  /- 0x00 _start: -/ jal ra 12,          -- call LLVMFuzzerTestOneInput(data, size)
  /- 0x04 -/         li a7 93,
  /- 0x08 -/         ecall,              -- exit(a0)
  /- 0x0c LLVMFuzzerTestOneInput: -/
                     beqz a1 56,         -- if size == 0 goto .LBB0_6 (→ 0x44)
  /- 0x10 -/         mv a2 a0,           -- p = data
  /- 0x14 -/         lbu a3 a0 0,        -- n = data[0]
  /- 0x18 -/         li a0 0,
  /- 0x1c -/         reject,             -- the length check (→ .LBB0_5 = 0x40)
  /- 0x20 -/         beqz a3 32,         -- if n == 0 goto .LBB0_5 (→ 0x40)
  /- 0x24 -/         li a0 0,            -- s = 0
  /- 0x28 -/         addi a2 a2 1,       -- p = data + 1
  /- 0x2c -/         add a3 a2 a3,       -- end = data + 1 + n
  /- 0x30 .LBB0_4: -/ lbu a1 a2 0,       -- t = *p                ← can this fault?
  /- 0x34 -/         addi a2 a2 1,       -- p++
  /- 0x38 -/         add a0 a0 a1,       -- s += t
  /- 0x3c -/         bne a2 a3 (-12),    -- if p != end goto .LBB0_4 (→ 0x30)
  /- 0x40 .LBB0_5: -/ ret,
  /- 0x44 .LBB0_6: -/ li a0 0,
  /- 0x48 -/         ret
]⟩

/-- `if (n > size) return 0;`  compiles to  `bltu a1, a3, .LBB0_5`  (size <u n) -/
def buggyProg : Program := harness (bltu a1 a3 36)

/-- `if (n >= size) return 0;` compiles to  `bgeu a3, a1, .LBB0_5`  (n >=u size) -/
def fixedProg : Program := harness (bgeu a3 a1 36)

/-! ## Fuzz it (by hand)

Try some inputs. Most are fine. The input `[1]` says "one byte of payload
follows" but none does, and `n = size` slips past the buggy check. -/
#eval (run buggyProg 1000 (load [])).show            -- exit(0)
#eval (run buggyProg 1000 (load [2, 10, 20])).show   -- exit(30)
#eval (run buggyProg 1000 (load [5, 10, 20])).show   -- exit(0): rejected, n > size
#eval (run buggyProg 1000 (load [1])).show           -- CRASH: Metal.Fault.badRead 0x00010001#32
#eval (run fixedProg 1000 (load [1])).show           -- exit(0)

/-! ## A crash is final

To prove "this binary does NOT satisfy the spec", it's not enough to show one
run of `n` steps crashes: `ExitsCleanly` says "there is SOME step budget after
which it has exited". We need: once you've crashed, no budget lets you exit.
That's true because `run` is deterministic: a longer run starts the same way.
The lemma, `fault_final`, lives in `S06_SymExec.lean` with its friends
`run_le` and `halted_unique`. Go read its proof; it's six lines. -/

/-! ## The counterexample, as a theorem

The negation of the spec, machine-checked. If you ever wondered what
"the proof found a bug" means concretely: this is the artefact. -/
theorem buggy_crashes : run buggyProg 12 (load [1]) = .fault (.badRead 0x10001) := by
  rfl

theorem buggy_violates_spec :
    ¬ ∀ input : List Byte, input.length < maxInput → ExitsCleanly buggyProg (load input) := by
  intro h
  exact fault_final _ _ _ _ buggy_crashes (h [1] (by decide))

/-! ## The spec for the fixed program

Stated here; proved in `Solutions/S07_Capstone.lean`. Your turn:
`Exercises/S07_Capstone.lean` has the same skeleton with `sorry`s.
The proof follows Stage 6 exactly: a prologue (two early exits and one path
into the loop), a loop invariant, an epilogue. The one new thing is that the
loop bound `n` comes *from the input* (it's `data[0]`), so the invariant has
to remember that `1 + n ≤ size` — which is precisely what the buggy check
fails to guarantee. -/
def FixedSpec : Prop :=
  ∀ input : List Byte, input.length < maxInput → ExitsCleanly fixedProg (load input)

end Metal
