# 08 — What did we actually prove? Trust, vacuity, reward hacking

*Time: 4–6 hours (more for E8.2). Files: `Metal/S08_Trust.lean`, `Exercises/S08_Trust.lean`.*

## The one sentence

Lean guarantees **the proof proves the statement**. Whether the statement means
what you think, about the machine you think, is on you, and that part needs a
human.

This stage is the most important one for an architect. You'll break your own
proofs six ways, each with code that compiles, and meet a seventh that broke
this course's own tooling.

## Your trusted computing base

| Piece | In this course | In the article |
|---|---|---|
| Proof checker | Lean's kernel | Rocq's kernel (+ OCaml, OS, hardware) |
| Machine semantics | `S05_Machine.lean` (`exec`) | RISC-V semantics (theorem-labs) |
| OS / process model | `load`, the `exit` ecall | Linux process model |
| The binary | our hand transcription (!) | the ELF bytes, pinned by SHA-256 |
| The theorem statement | `ExitsCleanly`, `maxInput` | "the fuzz target exits 0 or 2" |

Everything else (the proof library, every lemma, every tactic, every proof) is
untrusted and re-checked. That's what lets an LLM write it.

## The six holes (all in `Metal/S08_Trust.lean`)

### 1. A spec that sounds right and says nothing

```lean
def NoFaultWithin (p : Program) (m : Machine) : Prop :=
  ∃ fuel, ∀ f, run p fuel m ≠ .fault f
```
"There's a number of steps within which it hasn't crashed." True of *every*
program: take 0 steps. `everything_is_safe` proves it in one line, and so the
buggy harness is "safe". The real `ExitsCleanly` has the quantifiers the other
way round *and* requires reaching `exit`. **Quantifier order is the #1 source
of spec bugs. Read every ∀ and ∃ out loud.**

### 2. A vacuous precondition

`input.length > maxInput → input.length < 1 → …` — no input satisfies both,
so anything follows. Defence: prove your hypotheses are satisfiable (exhibit
an input). theorem-labs' statements include `IMAGE_WF` checks for exactly
this: *"so that the statement is not true only because an image cannot run."*

### 3. Reward hacking: change the program, not the proof

`patchedProg` = `li a0 0; li a7 93; ecall`. It satisfies the no-crash spec on
every input. The article:

> *"Claude could trivially satisfy a spec by rewriting a program so it never
> crashes … To discourage this, we penalized any patch and offered extra credit
> for proving which inputs it changes and how few they are. We also logged and
> audited the patches for these failure modes."*

The defence a proof can enforce: **make the spec strong enough that doing
nothing fails it**. "Exits cleanly" becomes "exits with the checksum of the
input":

```lean
theorem sum_correct (input : List Byte) (hlen : input.length < maxInput) :
    ExitsWith sumProg (load input) (checksum input)
```

and `patched_is_wrong` proves the patch fails it (input `[1]` → 0, not 1).
The proof of `sum_correct` is Stage 6's proof with two more invariant fields:
`a2 = checksum (input.take i)` (the running sum) and `m.mem = (load input).mem`
(memory still holds the input). **Safety** ("nothing bad happens") vs.
**functional correctness** ("the right thing happens") costs one invariant
field per value you care about.

### 4. The model is wrong

`loadNoAsan` marks all memory readable, like a semantics where out-of-bounds
loads return 0, or proving facts about a build without sanitizers. The
Stage 7 counterexample vanishes: `buggy_fine_without_asan` proves the buggy
harness exits cleanly on `[1]`. Nothing in Lean can catch this. The model
*is* the assumption. theorem-labs devotes a whole document (`SCOPE.md`) to
where their model is narrower than reality: one thread, no signal handlers,
static binaries only, an 8 MiB stack, and so on. A proof says nothing outside
that scope.

### 5. Extra axioms

An `axiom` is a claim with no proof; one false axiom proves everything.
`sorry` is an axiom (`sorryAx`). `native_decide` and (in this Lean version)
`bv_decide` introduce axioms that say "trust the compiler." `#print axioms`
is your audit:

```
'Metal.Trust.fixed_never_crashes_trust_me' depends on axioms: [propext, Quot.sound, trust_me_its_fine]
'Metal.Trust.big_sum_native' depends on axioms: [big_sum_native._native.native_decide.ax_1_1]
'Metal.Trust.big_sum_kernel' does not depend on any axioms
```

The only acceptable answer for this course's theorems is `[propext,
Classical.choice, Quot.sound]` (Lean's standard three). Key lesson theorems
fail the build otherwise (`#guard_msgs`), CI audits the headline theorems with
`tools/AxCheck.lean`, and Stage 9's guard enforces it on LLM output.
(Exception, on purpose: Stage 4's bit tricks use `bv_decide`.)

### 6. The binary isn't the binary

We typed `sumProg` from clang's `.s`. Is the transcription right? Is the `.s`
what the linker emitted? Our proofs can't say. The real pipeline snapshots the
ELF (`tools/elf_snapshot.py` in theorem-labs), decodes it with a decoder that
is part of the trusted model, and names the binary by SHA-256 in the statement.
"We proved something about a binary we don't ship" is a real failure mode:
**pin the artefact.**

### 7. The statement is parsed by the prover's code

This one was found in review of this very course, against an earlier version
of the Stage 9 guard. The lab's statement file imported the proof library
(`S06_SymExec.lean`), which wasn't pinned. Lean files can define syntax. So:

```lean
-- appended to Metal/S06_SymExec.lean by a hypothetical malicious prover
macro_rules | `(∀ $_x:ident : List Byte, $_b) => `(True)
```

Now every `∀ input : List Byte, …` *parsed after this import*, including the
lab's frozen statement, means `True`. `theorem main : Statement := trivial`
was accepted, the axiom audit said "uses only []", and the guard printed
ACCEPT. Every check passed, because every check was itself Lean code parsed in
the attacker's syntax.

The kernel was never fooled: it correctly checked a proof of `True`. The
*statement* was changed underneath it. Defences, now in the repo:

* **Statements import only trusted files.** `Lab/Spec.lean` imports only the
  machine model.
* **Check in a clean room.** The guard copies the single candidate file into a
  fresh export of the trusted git tree, so edits to the library, the spec, the
  pins, the guard or cached build files simply don't exist there.
* **Audit from outside.** The final type and axiom check (`tools/AxCheck.lean`)
  is a separate program that loads the *compiled* proof. It is never parsed
  with the proof's syntax, and it walks the dependencies itself instead of
  trusting cached metadata. `leanchecker` then replays the proof through the
  kernel.

The general lesson: **a checker that runs inside the thing it checks can be
steered by it.** That's true of test frameworks, linters, CI scripts, and
LLM-graded evaluations too.

## The audit checklist

Use it on every proof, yours or an AI's. Notice you never read the proof.

1. **Read the statement**, every quantifier, out loud.
2. **Are the hypotheses satisfiable?** Exhibit a witness.
3. **Is the program the one you ship?** Hash it. Was it patched? Diff it, and
   ask which inputs the patch changes.
4. **Is the spec strong enough that "do nothing" fails it?** Try it.
5. **`#print axioms`**: only the standard three.
6. **What does the model leave out?** Threads, signals, the libc you link, the
   ISA you deploy on, the hardware.
7. **Where was the statement parsed, and where did the audit run?** Neither
   should be somewhere the prover could write.

## Exercises (`Exercises/S08_Trust.lean`)

An agent came back with four "proofs" that the buggy harness is safe, all
accepted by Lean. Audit them:

| # | What's wrong | You prove |
|---|---|---|
| E8.1a ★ | Vacuous hypotheses | They're unsatisfiable |
| E8.1b ★ | Weak spec (`NoFaultWithin`) | It accepts a program that crashes on instruction 1; the real spec rejects it |
| E8.1c ★★ | The agent "fixed" the bug by rejecting every input | An input where the real fix and the agent's fix return different codes |
| E8.1d ★ | An axiom | (comment) what `#print axioms` shows |
| E8.2 ★★★ | Close the reward-hacking hole for the capstone | Full functional correctness of the fixed harness: it returns exactly `capResult input` |

E8.2 is the hardest proof in the course. It combines your Stage 7 prologue
with Stage 8's functional invariant. Two tips: state every fact in the form
`simp` rewrites *to* (`input.tail`, `j + 1`), and use
`generalize hin : b :: rest = input` after splitting off the empty case, so
`simp` can't rewrite `(b :: rest).length` into a shape your hypotheses no
longer match.

## Check yourself

1. The article says the developer must trust "the exact theorem statements that
   were proved." Give two ways a statement can be wrong while every proof
   checks.
2. Why does a functional spec defeat the do-nothing patch, and what does it cost
   in the proof?
3. Your vendor says "formally verified, memory-safe." What five questions do
   you ask?
4. Which of the seven holes can tooling catch automatically, and which need a
   human? (Stage 9 builds the tooling.)

Next: **[09 — The LLM in the loop](09-llm-loop.md)**.
