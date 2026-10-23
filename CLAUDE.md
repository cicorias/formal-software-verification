# Proofs to the Metal — repo guide for Claude

A course on formal verification for an experienced C/systems engineer, built
around Anthropic's "LLMs are making formal software verification feasible at a
much larger scale" (Oct 2026). Lean 4 (v4.35, **no Mathlib**), plus a Rocq bridge.

## Layout
- `docs/NN-*.md` — the narrative for each stage. Start at `docs/00-orientation.md`.
- `Metal/` — lessons (fully proved). `Metal/S05_Machine.lean` is the *trusted*
  machine model; `Metal/S06_SymExec.lean` is the untrusted proof library (`sym` tactic).
- `Exercises/` — the learner's workspace (`sorry` = hole). `Solutions/` — reference answers.
- `Lab/` — Stage 9: frozen `Spec.lean` + `Audit.lean`, editable `Proof.lean`.
- `c/` — the C sources, a random fuzzer, a Makefile (`make asm`, `make demo`).
- `rocq/` — Stage 10: the same ideas in Rocq.
- `tools/proof_guard.py` — decides whether a proof is acceptable. `tools/llm_prove.py` — API loop demo.

## Commands
- `lake build` — lessons + solutions (must be sorry-free; CI enforces).
- `lake build Exercises` — lists remaining `sorry`s.
- `python3 tools/proof_guard.py` — audit `Lab/Proof.lean`.
- `make -C rocq` — check the Rocq files.

## When tutoring
The learner is a senior C/low-level engineer with modest math. Prefer C and
assembly analogies over math notation. When they're stuck on an exercise, give
a hint that narrows the search (which lemma, which fact `sym` is missing)
before giving the answer; point at the stuck goal and ask what it needs.

## Rules
- Never edit a statement to make a proof go through. In `Exercises/`, only
  replace `sorry` (Stage 4 exercises may add `¬`, as instructed there).
- Never edit `Lab/Spec.lean`, `Lab/Audit.lean`, `Lab/guard.json`,
  `Metal/S05_Machine.lean` or `Metal/Guard.lean` unless the human explicitly asks;
  if the model changes, re-run `python3 tools/proof_guard.py --freeze` only on request.
- No `native_decide`/`bv_decide` in machine-level proofs (they add axioms); use `bv_omega`.
- If `lake build` hangs on a proof the editor accepted quickly, it's the kernel:
  checkpoint the machine state (see docs/06, "When the kernel is slow").
