# 09 — The LLM in the loop

*Time: 2–4 hours. Files: `Lab/`, `tools/proof_guard.py`, `tools/llm_prove.py`,
`.claude/skills/fv-prove/SKILL.md`, `Metal/Guard.lean`.*

## The architecture

```
             ┌─────────────── frozen, human-reviewed ───────────────┐
             │  Lab/Spec.lean    the program + reference + statement │
             │  Lab/Audit.lean   "main has exactly that type,        │
             │                    and only standard axioms"          │
             │  Metal/S05_Machine.lean   the model                   │
             └──────────────────────────┬───────────────────────────┘
                                        │ sha256 pinned in Lab/guard.json
  ┌──────────────┐   Lab/Proof.lean   ┌─▼──────────────────┐
  │    Claude    │ ─────────────────▶ │  proof_guard.py    │ ── ACCEPT ──▶ done
  │  (untrusted) │ ◀───────────────── │  + Lean kernel     │
  └──────────────┘   errors, goals    └────────────────────┘ ── REJECT ──▶ retry
```

The LLM does search. The guard decides. A human reviews three small files
once and never reads the proof.

## The guard (`tools/proof_guard.py`)

Three checks, in this order:

1. **Frozen files unchanged.** SHA-256 of `Lab/Spec.lean`, `Lab/Audit.lean`,
   `Metal/S05_Machine.lean`, `Metal/Guard.lean` must match `Lab/guard.json`.
   (A human runs `--freeze` after reviewing a change; an agent never should.)
2. **Proof hygiene, before building anything.** The editable file may not
   contain `sorry`/`admit`/`axiom`, `native_decide`/`bv_decide`, code that runs
   at build time (`#eval`, `run_cmd`, `initialize`), new syntax or macros,
   `unsafe`/`implemented_by`, or imports outside `Lab.Spec`/`Metal.*`.
   Comments are stripped first (nested `/- -/` too), so prose can't trip it
   and code can't hide in it.
   **Why check before building?** Because *building a Lean file runs code*.
   `#eval` and `initialize` execute at compile time. A proof file from an
   untrusted source is untrusted code; treat your build like CI for a PR from
   a stranger.
3. **The checker.** `lake build Lab.Audit` must succeed. `Audit.lean` contains

   ```lean
   example : Lab.Statement := Lab.main     -- exactly the frozen statement
   #assert_axioms Lab.main                -- only propext, Classical.choice, Quot.sound
   ```
   `#assert_axioms` is ~15 lines of Lean metaprogramming in `Metal/Guard.lean`
   (it calls `collectAxioms`).

It was tested against six attacks: proving `True` under the name `main`, adding
an axiom, `#eval` at build time, editing the statement to `input.length < 2`, a
`sorry` behind a nested comment, and the stub itself. All six were rejected,
and the honest proof was accepted:

```
ACCEPT: Lab.main proves the frozen statement, using only the standard axioms.
   axioms OK: Lab.main uses only [propext, Classical.choice, Quot.sound]
```

## The lab task

`Lab/Spec.lean`: clang's `count_zeros`, and the statement

```lean
def Statement : Prop :=
  ∀ input : List Byte, input.length < maxInput →
    ExitsWith czProg (load input) (countZeros input)
```

where `countZeros input = BitVec.ofNat 32 (input.countP (· = 0))`. Functional
correctness, so the do-nothing patch is impossible, and the reference is the
natural one (`countP`), not one shaped to match the loop, so the prover has to
bridge the two. A reference solution exists (it's about 100 lines, in the
style of `sum_correct`), but **it is deliberately not in this repo**, so the
lab stays a real test of whatever does the proving, you or a model.

## Three ways to run it

### A. Yourself

It's E6.3's invariant plus Stage 8's functional fields, and a lemma that
`countZeros (take (i+1))` equals `countZeros (take i)` plus whatever `seqz`
computes for byte `i`. Good final exam.

### B. Claude Code (the realistic way)

```sh
claude
> Use the fv-prove skill to prove Lab/Proof.lean. Don't stop until proof_guard accepts.
```

The `fv-prove` skill (`.claude/skills/fv-prove/SKILL.md`) gives Claude the
method (invariant struct → one-iteration lemma → induction → glue), the
rules, and the known gotchas. Claude gets a shell, so it can `#eval trace`,
build incrementally, read goals, and iterate. That's how the article's
proofs were produced, at scale and with a much bigger library. Watch what it
does: which lemmas it writes first, where it gets stuck, how it reads Lean's
errors. Then run the guard yourself.

### C. The bare loop (`tools/llm_prove.py`)

~150 lines that make the architecture explicit, using the Anthropic Python
SDK:

1. A system prompt with the rules and method, plus the **static context**
   (spec, model, library, two worked proofs), marked with `cache_control` so
   rounds 2+ pay the cache-read rate for it.
2. Claude returns a complete `Lab/Proof.lean`.
3. The guard runs. On rejection, its output and Lean's error messages go back
   as the next user turn.
4. Repeat up to `--rounds`. The script prints per-round token accounting
   (input / cache write / cache read / output).

```sh
pip install anthropic
python3 tools/llm_prove.py --rounds 8 --effort high
```

It uses `claude-opus-5-5`, streams responses, appends each assistant turn
unchanged (append-only history keeps the model's reasoning valid across
rounds), handles `refusal` stop reasons, and opts into server-side
`fallbacks: "default"`. It only writes `Lab/Proof.lean` and keeps a backup.
*Status:* syntax-checked and the SDK call signature verified against
`anthropic` 2.1.0; not run end-to-end in CI, since that needs credentials and
costs money.

Compare A, B and C. The difference between B and C is the article's point
about **tools and reuse**: an agent that can run `lake build` on one lemma at a
time, read a goal, and grep the library is far more token-efficient than one
that regenerates a whole file per round.

## Cost: what the article says, and what you'll see

* The article: proofs *"can take hundreds of millions of tokens to produce."*
  Cost is the main limitation.
* Newer models need fewer: on 36 small OSS-Fuzz verification tasks, *"Opus 5.5
  proves half of them with about 40% fewer tokens than Opus 5."*
* Reuse helps: with a shared workspace, *"agents needed 17% fewer tokens than
  when they worked alone,"* and the shared parts (runtime init, ASan) *"gained
  almost no new code."* In this repo, `S06_SymExec.lean` is that shared
  workspace, and the `fv-prove` skill is the accumulated know-how.
* The Mathlib analogy: Lean's maths library grew to nearly 300,000 theorems from
  over 700 contributors by building on itself. The authors expect verified
  software to compound the same way, along the dependency graph: verify libc,
  OpenSSL and curl once, and everything above them gets cheaper.

## Check yourself

1. Which of Stage 8's six holes does the guard close? Which can't it close, and
   why?
2. Why must the guard check the *source* for `#eval` instead of relying on the
   axiom audit?
3. The agent's proof is accepted. What, concretely, did a human have to review
   for that acceptance to mean anything?
4. Where would you put this guard in a real CI pipeline? What would you pin, and
   who may run `--freeze`?

Next: **[10 — Rocq, and reading the real thing](10-rocq-and-the-real-thing.md)**.
