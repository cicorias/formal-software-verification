# 10 — Rocq, and reading the real thing

*Time: open-ended. Files: `rocq/`, plus the theorem-labs repositories.*

You now know the ideas. This chapter gets you reading the article's actual
artefacts, and places the approach among the other tools you'll hear about.

## Part 1 — Lean ↔ Rocq

The article's proofs are in **Rocq** (formerly Coq). Same family as Lean:
dependent type theory, tactics, a small kernel. Most of what you learned
transfers directly. `rocq/Basics.v` is Stage 2 in Rocq; `rocq/Machine.v` is a
Stage 6-style proof in Rocq, written in the relational style the real model uses.

| Lean 4 | Rocq | Notes |
|---|---|---|
| `theorem foo : P := by tac` | `Theorem foo : P. Proof. tac. Qed.` | |
| `def` / recursive `def` | `Definition` / `Fixpoint` | |
| `inductive` | `Inductive` | |
| `structure` | `Record` | |
| `match x with \| p => e` | `match x with \| p => e end` | |
| `∀ x, P` · `∃ x, P` | `forall x, P` · `exists x, P` | |
| `∧ ∨ ¬ →` | `/\ \/ ~ ->` | |
| `List`, `x :: xs`, `[a, b]` | `list`, `x :: xs`, `[a; b]` | |
| `Nat` | `nat` | |
| `intro h` | `intros h` | |
| `exact e` / `apply f` | `exact e` / `apply f` | identical |
| `rfl` | `reflexivity` | |
| `simp [f]` | `simpl`, `unfold f`, `rewrite`, `autorewrite` | Rocq's `simpl` only computes; rewriting is explicit |
| `omega` | `lia` | |
| `decide` | `vm_compute; reflexivity` (closed facts), `lia` (arithmetic) | Rocq's `decide` is `decide equality`, a different tactic |
| `induction xs with \| nil => … \| cons x xs ih => …` | `induction xs as [\| x xs IH]` | |
| `induction xs generalizing acc` | `induction xs; intros acc` (state `acc` after `xs`) | |
| `cases h` · `obtain ⟨a, b⟩ := h` | `destruct h` · `destruct h as [a b]` | |
| `have h : P := by …` | `assert (h : P) by …` | |
| `constructor` · `⟨_, _⟩` | `constructor` / `split` · `exists _` | |
| `t <;> u` | `t; u` | Rocq's `;` applies to all goals |
| `sorry` | `admit.` / `Admitted.` | |
| `#print axioms foo` | `Print Assumptions foo.` | "Closed under the global context" = no axioms |
| `#eval` | `Compute` / `Eval vm_compute in` | Running code is less central in Rocq |
| `BitVec n` | `bv n` (stdpp), `word` (coqutil) | theorem-labs uses `bv` |

Do the three exercises in `rocq/Exercises.v` (`make -C rocq`). They're E2.9,
E2.10, and "prove a variant program safe", in Rocq.

## Part 2 — Functional vs. relational semantics

Our `step` is a function; theorem-labs' is a relation. From
`rocq-linux-process-semantics/theories/LinuxProcessSem/Run.v`:

```coq
Inductive step_to :=
  | SNext (c : config)
  | SError.

Inductive sstep : config -> list event -> step_to -> Prop :=
| sstep_instr : forall ms model ms' model',
    m_halted model = None -> ms_svc_pending ms = None ->
    mi_account_step ms model = MachineOk (ms', model') ->
    sstep (mkCfg ms model) [] (SNext (mkCfg ms' model'))
| sstep_instr_fault : ... MachineFault -> sstep (mkCfg ms model) [] SError
| sstep_syscall : ... syscall_spec (sys_input ms x8) model (Ok eff model' evs) -> ...
...
Inductive star : config -> list event -> config -> Prop :=
| star_refl : forall c, star c [] c
| star_step : forall c1 evs c2 tr c3,
    sstep c1 evs (SNext c2) -> star c2 tr c3 -> star c1 (evs ++ tr) c3.
```

Compare `rocq/Machine.v`: the same `sstep`/`star` shape, with `SNext`,
`SHalt`, `SError`, and a `s_load_fault` rule that plays ASan. Differences
worth understanding:

* **Events.** Every step emits observable events (bytes read and written,
  exit). Theorems compare *traces*, not just final states.
* **Nondeterminism.** A syscall spec is a *set* of permitted outcomes
  (`choose P`, `alt` in `Monad.v`): `read` may return any non-empty prefix of
  the available input; `mmap` may fail with `ENOMEM`; the stack address and
  `brk` are chosen at random (ASLR) and *quantified over* in the statements.
  So "the program never crashes" must hold for **every** execution, not one.
* **Coverage.** A case the model doesn't describe is `Unmodeled`, and the main
  statement requires that no execution reaches one: the proof can't escape
  into territory the model doesn't describe.

## Part 3 — A guided tour of the real model

Clone (it's ~15 MB; the proofs repo is several GB, skip it at first):

```sh
git clone --depth 1 https://github.com/theorem-labs/rocq-linux-process-semantics
```

Read in this order:

1. **`README.md`, "What a proof shows."** The main statement,
   `strong_universal_T` in `theories/EquivalenceDefinition/Equivalence.v`,
   relates a *source* and a *target* binary: for every input and every pair of
   launches, every execution of the source is covered by the model, and the two
   binaries' behaviours (sets of trace prefixes) are equivalent, unless the
   source always crashes. For OSS-Fuzz the source is the plain build and the
   target the sanitizer build: "they agree, and neither errors."
2. **The statements table.** `must_exit_with` and `halts_allowed_T` are our
   `ExitsWith`/`ExitsCleanly`, grown up. **`SPEC_PATCH_CLASSIFY*`** and
   **`weight_bound_T`** are how the article's *"extra credit for proving which
   inputs it changes and how few they are"* is made formal: a patch comes with
   a classifier of the inputs whose behaviour it changes, and a bound on how
   much of the input space that classifier accepts.
3. **`SCOPE.md`.** Where the model is narrower than Linux, the assumptions it
   does not check, and its known imprecisions. Our Stage 8 hole #4, written up
   honestly by the people who built it. Read it as a template for your own
   threat models.
4. **`theories/Riscv/Instr.v`.** The instruction AST. Note *"Immediates are kept
   at their encoded width … interpretation (sign-extension, shifting) is
   deferred to the semantics"*: the same choice as RV-lite. Then `Decode.v`
   (bytes → AST: the part we skipped) and `Sem.v`.
5. **`theories/Common/`.** The shared proof library, ~100 files:
   `SymTac.v`, `SymBranch.v`, `WalkTac.v` (symbolic execution, like our `sym`),
   `Asan*.v` (reasoning about the sanitizer runtime), `MuslStrlen.v`,
   `RefMemcpyLib.v` (libc routines every binary contains). This is the
   "shared workspace" that cut the article's token costs.
6. **`theories/Examples/`.** Worked proofs about small binaries.

Then the other two repos:

* **[theorem-labs/oss-verify](https://github.com/theorem-labs/oss-verify)** —
  how projects are enrolled; `docs/what-gets-proven.md` (the Halts and Agrees
  statements, the exit-status rules, the exact exceptions: leaks, MSan, one
  thread, 64 MiB); the `add-project` Claude skill that interviews a maintainer
  about what "correct" means and writes fuzz targets accordingly.
* **[theorem-labs/oss-verify-proofs](https://github.com/theorem-labs/oss-verify-proofs)** —
  the statements (each pinned to a binary by SHA-256 in a lock file) and the
  proofs. Big. Browse one project's `projects/<name>/` and `proofs/<name>/`.

## Part 4 — The landscape, for an architect

Where does "LLM writes interactive proofs about binaries" sit among the tools?

| Approach | Tools | You write | Machine does | Guarantees | Sweet spot |
|---|---|---|---|---|---|
| **Interactive proof, binary level** | Rocq/Lean + ISA/OS model (the article) | statement | (LLM) the proof; kernel checks | all inputs, about the actual binary | security properties of existing C/C++ |
| **Interactive proof, source level** | Isabelle (seL4), Rocq (CompCert), Lean | spec + proof | checks | all inputs, about a model of the source | kernels, compilers, crypto |
| **Auto-active (SMT)** | Dafny, **Verus** (Rust), F*, Why3, Frama-C/WP (C + ACSL), VeriFast | code + pre/postconditions + loop invariants | SMT discharges obligations | all inputs, source level | new code designed for verification |
| **Bounded model checking** | **CBMC** (C), Kani (Rust), ESBMC | harness + bound | exhaustive search up to N steps/bytes | all inputs *up to a bound* | C engineers' first formal tool; finds counterexamples |
| **Abstract interpretation** | Astrée, IKOS, Frama-C/Eva | nothing (config) | over-approximates all executions | no runtime errors (sound), with false alarms | avionics (Airbus), embedded C |
| **Design-level** | TLA+, P, Alloy | a model of the design | model-checks it | the *design* is right, not the code | distributed protocols |
| **Testing** | fuzzers, sanitizers, property tests | harness | samples | none, but finds lots | everything, always |

Notes:

* **Verus** is what the article used for its Rust Python-interpreter
  experiment (1.7 million random programs, 99.95% agreement with CPython).
  Auto-active tools are where most engineers should start *writing* verified
  code: you write invariants like ours and the SMT solver does the `sym` work.
* **CBMC** will feel most natural to you. Point it at a C function with
  `--bounds-check --pointer-check --unwind 64` and it either proves no
  violation within the bound or hands you a counterexample trace. Try it on
  `c/harness_buggy.c`.
* **Why binary-level?** It needs no rewrite into a verification language, and it
  doesn't trust the compiler: the theorem is about what runs. The costs are
  the model's size and the proof's length, and LLMs just made the second one
  cheap.
* **The compiler gap** that source-level tools leave open is what CompCert (a
  verified C compiler) closes from the other side.

## Part 5 — Where to go from here

Projects that extend this repo (each a good week):

1. **Close the transcription gap.** Write `encode : Instr → BitVec 32` and
   `decode : BitVec 32 → Option Instr` for RV-lite, prove
   `decode (encode i) = some i`, and state the theorems about decoded bytes.
2. **Writable memory.** Give `load` an output buffer with `canWrite`, transcribe
   a `memcpy`-style loop, and prove it never writes out of bounds.
3. **Words.** Add `lw`/`sw` (with alignment faults) to the model, re-freeze the
   guard, prove a word-at-a-time checksum. Then prove it equals the byte-wise
   one (differential, at machine level).
4. **The lab, with an agent.** Run Stage 9 option B and C; compare tokens and
   approaches.
5. **The real thing.** Build `rocq-linux-process-semantics` (≈45 CPU-minutes),
   step through an example proof, and try enrolling a small library of your own
   in OSS Verify.

Reading:

* *Theorem Proving in Lean 4* and *Functional Programming in Lean*
  (lean-lang.org/documentation): the official books.
* *Software Foundations*, vols. 1–2 (Pierce et al.): Rocq, from logic to Hoare
  logic. Volume 2 is Stage 6, done properly.
* Klein et al., *Comprehensive formal verification of an OS microkernel*
  (seL4): the 20-person-year baseline the article measures itself against.
* Leroy, *Formal verification of a realistic compiler* (CompCert).
* The article's appendix and expert commentary (linked from the article).

## Check yourself

1. Translate `induction xs generalizing acc with …` into Rocq.
2. Why does a nondeterministic model force "for all executions" statements, and
   why does ours get away with "there exists an execution"?
3. What do `SPEC_PATCH_CLASSIFY` and `weight_bound_T` add to the article's
   defence against reward hacking that a functional spec doesn't?
4. Your team ships embedded C. Rank CBMC, Frama-C, Astrée and the article's
   approach for (a) a parser of untrusted input, (b) a control loop, (c) a
   distributed configuration protocol. Justify each.
