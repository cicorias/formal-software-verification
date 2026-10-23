# Proofs to the Metal

**A hands-on course in formal software verification for C and systems engineers**,
built around Anthropic's
[*LLMs are making formal software verification feasible at a much larger scale*](https://www.anthropic.com/research/formal-verification)
(Oct 2026).

In that work, Claude proved that 239 fuzz-test entry points across 123 open-source
C/C++ libraries **never crash on any input under 64 MB**, as theorems about their
RISC-V machine code, checked by the Rocq proof assistant, finding and fixing
hundreds of bugs along the way. This repo teaches you to do the same thing, end to
end, on programs small enough to understand completely:

```
uint32_t LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) { ... }
        │  clang --target=riscv32 -O1
        ▼
0x14: lbu  a3, 0(a0)    0x1c: bltu a1, a3, .reject   ← the off-by-one, as one instruction
        │  transcribe into a formal RISC-V model (Lean)
        ▼
theorem fixed_never_crashes :
  ∀ input, input.length < 64 MiB → ExitsCleanly fixedProg (load input)     ✓ checked by Lean's kernel
```

Everything here is executable and machine-checked: every lesson builds, every
exercise has a verified solution, and CI keeps it that way.

## Who it's for

Experienced engineers who think in C, pointers and assembly, and whose maths is
"fine, but it's been a while." No prior proof-assistant experience. Every
concept is introduced through a C or assembly analogy; the maths is limited to
induction, which you already use every time you reason about a loop.

## Language: Lean 4 (+ a Rocq bridge)

The course is built in **Lean 4** (pinned to v4.35, no Mathlib): it's both a
programming language and a prover, so the RISC-V model you prove things about
is one you can also run, trace and disassemble in the same file. The article
used **Rocq**; Stage 10 translates everything and walks you through the real
Rocq model. Why Lean is the better learning vehicle: [docs/01](docs/01-lean-for-c.md).

## The stages

| # | Stage | You'll be able to… | Article tie-in | Time |
|---|---|---|---|---|
| 0 | [Orientation](docs/00-orientation.md) | explain the article's pipeline, what's trusted, and why LLMs fit | the whole thing | 45 m |
| 1 | [Lean for C programmers](docs/01-lean-for-c.md) | write structs, tagged unions, recursion, byte buffers | — | 2–3 h |
| 2 | [Proofs are programs](docs/02-proofs.md) | prove things with `rfl`, `omega`, `simp`, induction; **generalise the hypothesis** | "the proof checker" | 4–6 h |
| 3 | [Specifications](docs/03-specs.md) | write round-trip/differential/bound specs; see a fuzzer miss a bug a proof finds | fuzz targets as specs; LZO round-trip | 4–5 h |
| 4 | [Bits and overflow](docs/04-bits.md) | settle overflow questions for all 2^64 inputs; extract counterexamples | counter underflow, OOB | 3–4 h |
| 5 | [A machine](docs/05-machine.md) | read and run a formal RISC-V semantics with an ASan shadow map | "RISC-V and Linux process models" | 3–4 h |
| 6 | [No crash, for all inputs](docs/06-no-crash.md) | prove a clang-compiled loop never faults: invariants, symbolic execution | the 600k-line proofs, in miniature | 6–8 h |
| 7 | [Capstone](docs/07-capstone.md) | harness → bug → machine-checked counterexample → fix → proof | "found hundreds of bugs, patched, re-proved" | 6–10 h |
| 8 | [Trust](docs/08-trust.md) | break proofs six ways: vacuity, weak specs, reward hacking, model bugs, axioms | "verified ≠ bug-free"; reward hacking | 4–6 h |
| 9 | [LLM in the loop](docs/09-llm-loop.md) | gate an AI's proofs with a frozen statement + axiom audit; run Claude on a lab | Claude as prover; tokens; reuse | 2–4 h |
| 10 | [Rocq and the real thing](docs/10-rocq-and-the-real-thing.md) | read theorem-labs' model; place the approach among CBMC, Dafny, Verus, Astrée… | Rocq, Verus, the roadmap | open |

Also: [setup](docs/setup.md) · [cheat sheet](docs/cheatsheet.md).

## Quick start

```sh
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh   # Lean toolchain manager
source ~/.elan/env          # or open a new shell, so `lake` is on your PATH
git clone https://github.com/cicorias/formal-software-verification && cd formal-software-verification
lake build                  # all lessons + solutions (≈1 min first time)
code .                      # VS Code + the "lean4" extension; open Metal/S01_LeanForC.lean
```

Then read [docs/00-orientation.md](docs/00-orientation.md). Full details,
including Nix and Rocq: [docs/setup.md](docs/setup.md).

## How to work through it

For each stage:

1. **Read** `docs/NN-*.md`: the concepts, with C analogies.
2. **Step through** `Metal/SNN_*.lean` in the editor, cursor on each line, watching
   the infoview. Every lesson is complete and fully proved.
3. **Do** `Exercises/SNN_*.lean`: replace each `sorry`. Check with
   `lake build Exercises.SNN_…`; you're done when no `sorry` warnings remain.
   Exercises are graded ★ / ★★ / ★★★.
4. **Compare** with `Solutions/SNN_*.lean`, after you've tried.
5. **Answer** the "Check yourself" questions at the end of the doc, without
   looking. They're the part that makes it stick.

## Repository layout

```
docs/          the narrative, one chapter per stage
Metal/         lessons (Lean). S05_Machine.lean is the TRUSTED machine model;
               S06_SymExec.lean is the untrusted proof library (the `sym` tactic)
Exercises/     your workspace: 70 holes across 8 stages
Solutions/     reference solutions (CI-checked: no sorry; headline theorems axiom-audited)
Lab/           Stage 9: frozen Spec.lean + Audit.lean, editable Proof.lean
c/             the C sources, a random fuzzer, `make asm` / `make demo`
rocq/          Stage 10: Basics, a relational machine, exercises (Rocq 9)
tools/         proof_guard.py (accept/reject a proof), llm_prove.py (API loop demo)
.claude/       the fv-prove skill for Claude Code;  CLAUDE.md: repo guide for Claude
```

## What's verified, concretely

* `Metal.sum_never_crashes` — clang's `sum` loop never faults, all inputs < 64 MiB.
* `Metal.Trust.sum_correct` — …and returns exactly the byte checksum.
* `Metal.buggy_violates_spec` — the off-by-one harness provably crashes (on `[1]`).
* `Metal.S07Solution.fixed_never_crashes` — the one-instruction fix provably doesn't.
* `Metal.S08Ex.e8_2` — the fixed harness returns exactly the payload sum, all inputs.
* `Metal.S03.decode_encode` — RLE round-trip, all inputs (the buggy encoder passes
  200,000 random tests and is disproved by one).
* All of these use only Lean's three standard axioms. CI audits them with
  `tools/AxCheck.lean`, and several lesson files also fail the build otherwise
  (`#guard_msgs`). The Stage 4 bit-trick theorems deliberately use `bv_decide`,
  which adds a native-code axiom; docs/04 explains the trade.

## Using Claude Code as a tutor

`CLAUDE.md` tells Claude about the repo and the learner, and to give hints that
narrow the search before giving answers. Useful prompts: *"explain the goal at
line 84"*, *"why is `sym` stuck here?"*, *"give me a hint for E6.3, not the
answer."* Stage 9 is where you deliberately hand it the whole job.

## Status and honesty notes

* Built and checked with Lean 4.35.0 and Rocq 9.1.1. Tactic behaviour changes
  between Lean versions; use the pinned toolchain.
* RV-lite is a teaching model: an RV32I subset, one syscall, an AST instead of
  a decoder, the input buffer as the only data memory. Docs 05 and 08 list
  exactly what that costs.
* `tools/llm_prove.py` has been syntax-checked against the `anthropic` SDK
  (2.1.0) but is not run in CI (it needs credentials and costs money).
* The Stage 9 lab has a verified reference solution that is intentionally *not*
  in the repo.

## Credits

The ideas, numbers and pipeline are from the Anthropic / Theorem article and
from theorem-labs' open repositories
([rocq-linux-process-semantics](https://github.com/theorem-labs/rocq-linux-process-semantics),
[oss-verify](https://github.com/theorem-labs/oss-verify)). This course is an
independent educational companion and isn't affiliated with either.
