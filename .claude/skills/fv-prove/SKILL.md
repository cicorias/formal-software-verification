---
name: fv-prove
description: Prove a frozen Lean theorem about an RV-lite (RISC-V) program in this repo, e.g. the Stage 9 lab in Lab/Proof.lean, using the sym-tactic proof library and the proof guard. Use when asked to "prove the lab", "fill the sorry in Lab/Proof.lean", or prove that a transcribed binary never crashes / returns the right value.
---

# Prove a machine-level theorem

You are the untrusted half of the article's pipeline: you search for a proof,
and `tools/proof_guard.py` (frozen statement + Lean's kernel + an axiom audit)
decides whether it counts. Your output is worthless unless the guard says ACCEPT.

## Ground rules
- Read the statement in `Lab/Spec.lean`. Do not edit it, `Lab/Audit.lean`,
  `Lab/guard.json`, or anything in `Metal/`. Write only `Lab/Proof.lean`.
- No `sorry`, `axiom`, `native_decide`, `bv_decide`, `#eval`, macros or new
  syntax. Imports: `Lab.Spec` and `Metal.*` only.
- Don't read `Solutions/` for the lab; there is no lab solution there anyway.

## Method (it works; follow it)
1. Run the program on small inputs to see its shape:
   `#eval trace Lab.czProg [0, 5, 0]` (from `Metal.S05_Playground`) in a scratch file.
2. Identify the loop head pc, and write an invariant `structure` with one field
   per fact: pc, each live register as a function of the iteration `i`, `ra`,
   `canRead = inInput input.length`, and — for functional specs — the
   accumulator register and `m.mem = (load input).mem`.
3. One-iteration lemma: `∃ m', run p K m = .running m' ∧ (if i+1 = len then <exit facts> else Inv (i+1) m')`.
   Gather facts first (`inInput_of_lt`, `addr_succ_eq_iff`, `load_mem`, a
   lemma for how the accumulator grows), then `by_cases h : i + 1 = len` and
   `sym [prog, inv.pc, inv.a0, …, h]` in each branch. Prove the new invariant
   with `refine ⟨?_, …⟩ <;> sym [...]`.
4. Loop lemma by `induction k` on iterations remaining — copy the shape of
   `Metal.loop_all` in `Metal/S06_NoCrash.lean` / `Metal.Trust.sum_loop`.
5. Prologue (`∃ m, run p N (load input) = .running m ∧ Inv input 0 m`),
   epilogue, glue with `run_add_of_running`. Treat the empty input separately.
6. `lake build Lab.Proof` after each lemma. When `sym` leaves a goal, read it:
   it names the missing fact. State facts in simp-normal form
   (`input.tail`, `j + 1`, `4294967295#32` for `-1`).
7. Finish with `python3 tools/proof_guard.py`. Only ACCEPT counts.

## Gotchas
- If the editor is fast but `lake build` hangs: the kernel is re-deriving
  register values through `load` with a big constant. Checkpoint the state into
  an `∃ m, …` lemma and continue from the abstract `m`.
- `simp` turns `BitVec.ofNat 32 len == 0` into `input = []`: pass `input ≠ []`.
- Exit codes: if `sym` leaves `x = ?m`, give the code explicitly.
