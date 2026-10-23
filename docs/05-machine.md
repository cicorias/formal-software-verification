# 05 — A machine you can prove things about

*Time: 3–4 hours. Files: `Metal/S05_Machine.lean` (the model), `Metal/S05_Playground.lean`
(using it), `Exercises/S05_Machine.lean`, `c/`.*

## Why this stage exists

The article proves facts about **binaries**: what the CPU actually executes,
after the compiler has done whatever it does. To do that you need a precise,
formal description of the CPU and the OS: the **semantics**. In the article it
is theorem-labs' `rocq-linux-process-semantics`, a Rocq model of a Linux
process running RV64GC (about 220k lines of Rocq, counting its proof library and
examples). Here it is
**RV-lite**: ~200 lines of Lean that you can read in one sitting, and that you
will trust for the rest of the course.

## What's in RV-lite

```
 Machine = { regs : Reg → Word         -- x0..x31; x0 reads as 0
             pc   : Word
             mem  : Word → Byte        -- all 4 GiB
             canRead, canWrite : Word → Bool }   -- the ASan shadow map
```

* **Instructions**: `lui addi andi sltiu slli srli add sub and or xor sltu lbu
  sb beq bne blt bge bltu bgeu jal jalr ecall`, plus assembler pseudo-ops (`li
  mv ret beqz bnez seqz j`) so programs read like `objdump`. Immediates keep
  their encoded width (12/13/20/21 bits) and are **sign-extended** in the
  semantics, as the hardware does.
* **`exec : Instr → Machine → Outcome`**: one rule per instruction, transcribed
  from the ISA manual. `Outcome` is `running m'` / `halted code` / `fault f`.
* **Faults** are our crashes: fetching where there's no code (SIGSEGV), a
  load/store whose shadow bit is off (an ASan report), or a syscall the model
  doesn't cover (theorem-labs calls this `unmodeled`).
* **The OS**: one syscall, `exit` (a7 = 93, the real Linux number).
* **`run : Program → Nat → Machine → Outcome`**: run with *fuel*. Lean needs
  termination, so we give a step budget; `halted` and `fault` are final.
* **The process model**: `load input` builds the initial state for
  `LLVMFuzzerTestOneInput(data, size)`: `a0 = 0x10000`, `a1 = size`, and *only
  the input bytes* readable. Reading one byte past the end is a fault: ASan's
  redzone.
* **The spec**: `ExitsCleanly p m := ∃ fuel code, run p fuel m = .halted code`.
  Since a fault stops `run` with `.fault`, reaching `.halted` means no fault on
  the way. `ExitsWith` adds "with this exit code".

### Design choices, and what they cost

Every simplification is a place where our theorems say less than they seem to.
Stage 8 comes back to each.

| Choice | Real model | Cost of our simplification |
|---|---|---|
| Instructions are an AST | Decoder from bytes is part of the model | We trust our hand transcription of clang's `.s` |
| Code separate from data | Code lives in memory | No self-modifying code (fine) |
| Only input bytes readable | Full address space, `mmap`, stack, heap, ASan allocator | No heap/stack bugs representable |
| One syscall | ~hundreds, each a *set* of permitted outcomes | No I/O, no `read` returning short counts |
| Deterministic | Nondeterministic (ASLR, `mmap` placement, syscall failures) | Our "∃ an execution" = "all executions" |
| No alignment faults, no CSRs, one hart | RV64GC, still one thread | Fine for this course |

### Functional vs. relational semantics

Ours is a *function*: `step` returns the next state. Theorem's is a
*relation*: `sstep : config → list event → step_to → Prop` says which next
states are *permitted*. A relation can say "the kernel may return any
non-empty prefix of the input to `read`," which a function can't. The price:
the theorems must quantify over *every* execution. Stage 10 shows the
relational style in Rocq.

## Walk-through

**`S05_Machine.lean`** — read `exec` line by line next to the
[RISC-V unprivileged spec](https://riscv.org/specifications/). Ask of each rule:
"is that really what the hardware does?" That question is the whole job of
reviewing a semantics. Things to notice:

* `reg` returns 0 for x0; writes to x0 are stored and never observed.
* `jalr` clears bit 0 of the target (`&&& ~~~1`).
* `lbu` zero-extends; `sb` truncates.
* Branch targets are `pc + sext(off)`: PC-relative, in bytes.

**`S05_Playground.lean`** — your simulator:

* `Program.disasm` — `objdump -d`.
* `trace prog input` — single-step with registers, like `gdb` with `display`.
* `exitCode prog input` — run and report.
* `minusOne` / `firstByte` — sign- vs. zero-extension.
* `lastByteProg` — clang's `last_byte`, which reads `p[-1]` on empty input:

`#eval trace lastByteProg [10, 20, 30]` prints, in execution order:
```
0x0: jal ra, 12   ⟹ a0=0x10000 a1=0x3 a2=0x0 a3=0x0
0xc: add a0, a0, a1   ⟹ a0=0x10003 a1=0x3 a2=0x0 a3=0x0
0x10: lbu a0, -1(a0)   ⟹ a0=0x1e a1=0x3 a2=0x0 a3=0x0
0x14: jalr zero, 0(ra)   ⟹ a0=0x1e a1=0x3 a2=0x0 a3=0x0
0x4: addi a7, zero, 93   ⟹ a0=0x1e a1=0x3 a2=0x0 a3=0x0
0x8: ecall   ⟹ exit(30)
```
and on `[]`, `(run lastByteProg 100 (load [])).show` is
`CRASH: Metal.Fault.badRead 0x0000ffff#32`: address 0xFFFF, one below `inputBase`.

* `example … := by rfl` — **a test inside the prover**: the kernel runs the
  program on one input and checks the result. Exactly as strong as one fuzzer
  execution, no more. Stage 6 is the jump from one input to all of them.

## Where the programs come from

```sh
make -C c asm      # clang --target=riscv32-unknown-elf -march=rv32i -mabi=ilp32 -O1 -S
```
`c/build/sum.s`, `harness_*.s`, `examples.s`. We transcribe them by hand into
Lean (`sumProg`, `fixedProg`, …), computing branch offsets as
`target − branch address`. The real pipeline doesn't transcribe: it snapshots
the ELF and decodes the bytes with a decoder that is itself part of the
trusted model, and pins the binary by SHA-256.

## Exercises (`Exercises/S05_Machine.lean`)

| # | What |
|---|---|
| E5.1 ★ | Predict exit codes of six tiny programs (sign extension, x0, `sltu`, the `lui`+`addi 0x800` trap, `jalr` bit 0, a loop). Write the prediction down **before** running. |
| E5.2 ★★ | Transcribe clang's `count_zeros` and make its tests pass. You compute the offsets. |
| E5.3 ★★ | Transcribe `max_byte` (a branch inside the loop, two `j`s). |
| E5.4 ★ | Find the input that crashes `lastByteProg` and state the exact fault. |

## Check yourself

1. Which single line of `exec` would you change to model a CPU where loads
   don't check permissions? What would happen to every theorem in Stages 6–7?
2. Why must `run` take fuel? What does `run p 0 m = .running m` mean for a spec
   that says "∃ fuel, …"?
3. `lui a0, 1; addi a0, a0, 0x800` gives 2048, not 6144. Why, and what do
   assemblers do about it?
4. Name three behaviours of a real Linux process that RV-lite can't express.

Next: **[06 — Proving a compiled loop never crashes](06-no-crash.md)**.
