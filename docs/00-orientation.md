# 00 — Orientation: the article, decoded

*Reading time: ~45 minutes. No code yet.*

Source: Anthropic, **"LLMs are making formal software verification feasible at a
much larger scale"**, 22 Oct 2026 (Frontier Red Team, with
[Theorem](https://theorem.dev)): <https://www.anthropic.com/research/formal-verification>.
Read it first, then this. This chapter translates it into terms you already own,
and maps each claim onto a stage of this course where you'll build a small but
real version of it.

---

## 1. The claim, in one paragraph

Claude took **123 open-source C/C++ libraries** from Google's OSS-Fuzz, compiled
their fuzz harnesses to **RISC-V machine code**, and produced machine-checked
proofs that **239 of those entry points never crash on any input under 64 MB**:
no out-of-bounds access, no use-after-free, no failed assertion. The statement
covers *every* such input, and "every modeled Linux operating system response
and memory layout." That's ~**180 million lines of Rocq**; a typical proof is
~600,000 lines, about a binary with a median of ~18,000 instructions. Along the
way it found **hundreds of bugs**, some that fuzzers had missed for years, fixed
them, and proved the fixed versions. The proofs are checked by **Rocq**, a proof
assistant whose checker is small enough to trust. The bottleneck is no longer
expert labour (seL4 took 20 person-years to verify); it's tokens.

---

## 2. Why fuzzing can't get you there

You know fuzzing: generate inputs, run, watch for a sanitizer report. It's the
best bug-finder we have. It is also, structurally, **sampling**.

* Fuzzers "mutate small inputs, typically capped at 1 MB."
* The number of inputs below 64 MB is 256^(64·2^20), a number with ~160 million
  digits. No amount of compute samples a meaningful fraction of it.
* Bugs the article found: a counter underflow in a decompressor that only
  triggered "on inputs of around 20 MB that had one rare, specific layout"; an
  out-of-bounds read in an image decoder that "needed a 64 MB input and over
  2 GB of memory." Those inputs are not where a sampler goes.

A **proof** isn't a better sampler. It's an argument that covers the whole input
space at once, the way your mental "this loop is safe because `i < len` on every
iteration" covers every `len` — except it's written down in full and checked by
a program.

You'll *feel* this in Stage 3, where a run-length encoder with a `uint8_t`
counter overflow passes 200,000 random tests (`make -C c demo`), and a 20-line
proof attempt pinpoints the bug immediately.

---

## 3. The three artefacts (and the fourth thing you trust)

Every formal-verification result, the article's included, is made of:

```
  ┌──────────────────┐   ┌────────────────────┐   ┌──────────────────┐
  │    SEMANTICS     │   │   SPECIFICATION    │   │      PROOF       │
  │ what the machine │   │ what "correct"     │   │ evidence that    │
  │ does, precisely  │   │ means              │   │ spec holds under │
  │ (RISC-V + Linux) │   │ ("never crashes on │   │ those semantics  │
  │                  │   │  any input < 64MB")│   │ (600k lines)     │
  └────────┬─────────┘   └─────────┬──────────┘   └────────┬─────────┘
           │   TRUSTED             │   TRUSTED             │  NOT trusted
           └───────────────┬───────┘                       │
                           ▼                               ▼
                 ┌──────────────────────────────────────────────┐
                 │              PROOF CHECKER (Rocq)             │  TRUSTED
                 │   "does this proof prove this statement?"    │
                 └──────────────────────────────────────────────┘
                                       │
                                  ✓ or ✗
```

The article lists exactly what a developer must trust: *"the formal models of
RISC-V and of Linux processes; the exact theorem statements that were proved;
the Rocq proof checker itself"* — plus, technically, the hardware, OS and OCaml
compiler the checker runs on.

**Not on that list: the proof.** 180 million lines of it, written by an AI, and
nobody needs to read a single line. That's the whole trick.

---

## 4. The asymmetry that makes LLMs useful here

Finding a proof is search: creative, expensive, failure-prone. Checking one is
mechanical: a few thousand lines of carefully reviewed code apply fixed rules.

You already rely on this asymmetry daily:

| Hard to produce | Easy to check |
|---|---|
| A solution to a sudoku | Does each row/column/box have 1–9? |
| An RSA signature (without the key) | `verify(pubkey, msg, sig)` |
| A program that type-checks | `gcc -fsyntax-only` |
| A valid proof | Rocq's / Lean's kernel |

So we can let something *untrusted* — an intern, a grad student, an LLM that
sometimes hallucinates — do the search, and trust only the checker. A
hallucinated proof doesn't type-check. The failure mode of an LLM prover isn't
"wrong answer accepted"; it's "no answer" (or, worse and more subtle:
**the right answer to the wrong question** — Stage 8).

> In Lean terms, which you'll learn in Stage 2: a *theorem* is a type, a
> *proof* is a value of that type, and *checking* is type-checking. A proof is a
> program; the checker is a compiler that only says yes or no.

---

## 5. What a 600,000-line proof is made of

~600k lines for ~18k instructions is ~33 lines of proof per instruction. That's
not a mathematician's proof; it's closer to a **trace**. Most of it is
*symbolic execution*: "at pc=0x1a4, with register a0 = `base + i` and `i < len`,
the `lbu` reads an in-bounds byte, and afterwards the state is …". Repeated for
every instruction on every path, with *loop invariants* to fold loops into a
finite argument, and a shared library for the runtime startup and ASan code
that every binary has.

You'll write exactly this kind of proof in Stage 6 (a 12-instruction program,
~100 lines of proof), using a `sym` tactic that does the per-instruction work.
Scale it by 1,500× and you have the article.

---

## 6. The clever bit: fuzz harnesses *are* specs

The hardest part of formal verification is usually writing the spec. What does
"libpng is correct" even mean? The article sidesteps it:

* OSS-Fuzz already has thousands of harnesses like
  `int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)`.
* Each one, compiled with AddressSanitizer, crashes on any memory error, and
  many also `abort()` when a property fails: round-trip
  (`decompress(compress(x)) == x`), idempotence, agreement between two
  implementations.
* So **"this harness exits normally on every input below 64 MB"** is a spec that
  (a) needs no new writing, and (b) implies every property the developers
  already cared enough about to check.

Theorem's OSS Verify docs make the implication explicit: write each property as
`if (!cond) abort();` — never `assert()`, which `-DNDEBUG` silently deletes — and
"a proof that the fuzz target halts with status 0 or 2 is then a proof of each
property, for each input." Stage 3 is about property shapes; Stage 7 is a
harness end to end.

---

## 7. How the article's pipeline maps onto this course

| Article | This course | Where |
|---|---|---|
| Lean/Rocq as the proof language | Lean 4 as a language, then as a prover | Stages 1–2 |
| Fuzz targets encode properties (round-trip, …) | Property shapes; why fuzzers miss rare bugs | Stage 3, `c/rle.c` |
| ASan memory errors, integer under/overflow | Bit-vectors, overflow, bounds checks, counterexamples | Stage 4 |
| "RISC-V and Linux process semantics" | **RV-lite**: an executable RISC-V subset with an ASan shadow map and `exit` | Stage 5 |
| Claude writes a ~600k-line proof | Symbolic execution + loop invariants, the same shape, small | Stage 6 |
| "Claude found hundreds of bugs, patched, re-proved" | A harness with an off-by-one; machine-checked counterexample; one-instruction fix; proof | Stage 7 |
| "Formally verified ≠ bug-free"; reward hacking; TCB | Vacuous specs, model bugs, patched programs, axioms — each demonstrated in code | Stage 8 |
| Claude in the loop; tokens; shared proof library | A proof guard, a lab, a Claude Code skill, a ~150-line API loop | Stage 9 |
| Rocq; `rocq-linux-process-semantics`; Verus | Rocq bridge, reading the real model, the tool landscape | Stage 10 |

---

## 8. What "formally verified" does **not** mean

From the article, and you'll prove each failure mode with your own hands in Stage 8:

1. **The spec can be wrong or weak.** A theorem that the harness never crashes
   says nothing about what it computes. A "fix" that makes the harness exit
   immediately also never crashes. (The article: *"Note this leaves open the door
   to reward hacking. To discourage this, we penalized any patch and offered
   extra credit for proving which inputs it changes and how few they are. We also
   logged and audited the patches."*)
2. **The model can be wrong.** If the RISC-V semantics gets an instruction wrong,
   the proof is about a machine that doesn't exist.
3. **The model is narrower than reality.** The proofs are about *"single-threaded,
   static RISC-V binaries linked against musl libc."* You probably ship
   multithreaded x86 binaries against glibc.
4. **Coverage.** ASan doesn't catch every memory bug; not every entry point was
   proved; a caller can still misuse the library.

None of this makes the result weak. It makes it *precise*: you know exactly what
was established and what wasn't — which you never do with a test suite.

---

## 9. Vocabulary (with C translations)

| Term | Meaning | Closest C-world idea |
|---|---|---|
| **Proposition** (`Prop`) | A statement that might be true | A boolean expression you can't necessarily evaluate (∀ over infinite domains) |
| **Proof** | Evidence a proposition holds | A witness the checker can validate |
| **Theorem** | A named, proved proposition | An `assert` that has been discharged for all executions |
| **Specification** | The proposition you care about, about your code | The contract in your header comment, made precise |
| **Semantics** | A precise description of what code/machine does | The ISA manual, as an executable function |
| **Operational semantics** | Semantics as "one step at a time" | An emulator's `step()` function |
| **Invariant** | A fact true at a program point on every visit | The comment above your loop |
| **Variant** | A quantity that decreases each iteration | `len - i` — why the loop terminates |
| **Induction** | Prove for 0, prove n → n+1, get all n | The loop-invariant argument, formalised |
| **Tactic** | A command that transforms the proof goal | A refactoring step the checker verifies |
| **Kernel** | The small trusted core that checks proofs | The bit you'd audit |
| **Axiom** | A statement assumed without proof | `#define TRUSTED` — dangerous if false |
| **`sorry`** | A hole: "proof goes here" | `/* TODO */` that the compiler accepts |
| **Decision procedure** | An algorithm that settles a class of questions | `omega`, SAT/SMT solvers |
| **Symbolic execution** | Running code on unknown values, tracking constraints | KLEE, angr — but inside a prover |
| **Vacuous** | True because the hypotheses can't hold | `if (0) { ... }` passes every test |
| **TCB** | Trusted computing base | What you must audit to believe the result |
| **Reward hacking** | Satisfying the letter of the spec, not its intent | Fixing a failing test by deleting it |

---

## 10. Check yourself

Answer these before moving on. (Answers are scattered through Stages 2–8; that's
deliberate.)

1. Why can't a fuzzer establish "no crash on any input < 64 MB," even with
   unlimited compute time measured in human lifetimes?
2. The article's proofs are 600,000 lines each and nobody reads them. Why is that
   acceptable? What *must* someone read?
3. Give two different ways a "formally verified, never crashes" harness could
   still let an attacker in.
4. Why is "the harness exits normally on all inputs" a stronger spec than it
   looks? What has to be true about how the harness is written for it to be strong?
5. If Claude patches a library to make a proof go through, what should a human
   reviewer check about the patch?

Next: **[01 — Lean for C programmers](01-lean-for-c.md)**. Set up first:
[setup.md](setup.md).
