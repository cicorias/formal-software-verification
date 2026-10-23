# Cheat sheet

## Lean for C programmers

| C | Lean |
|---|---|
| `uint32_t x = 5;` | `let x : BitVec 32 := 5` (or `5#32`) |
| `x + y` (wraps) | `x + y` on `BitVec` / `UInt32` |
| `(unsigned long long)x` as a true integer | `x.toNat` |
| `(int32_t)x` | `x.toInt` |
| `a < b` unsigned / signed | `a < b` / `a.slt b` |
| `(int32_t)(int8_t)b` | `b.signExtend 32` |
| `(uint32_t)(uint8_t)b` | `b.zeroExtend 32` |
| `& \| ^ ~ << >>` | `&&& \|\|\| ^^^ ~~~ <<< >>>` |
| `struct` | `structure` |
| tagged union + `switch` | `inductive` + `match` |
| `NULL` / error code | `Option` / `Except` |
| `for` loop | recursion / `List.foldl` |
| `buf[i]` (unchecked) | `xs[i]?` (Option) or `xs[i]` (needs proof `i < xs.length`) |
| `assert(p)` | `have h : p := by …` (checked for *all* executions) |
| `/* TODO */` | `sorry` |

## Tactics

| Goal looks like | Try |
|---|---|
| concrete computation | `rfl`, `decide`, `decide +kernel` |
| linear arithmetic on `Nat`/`Int` | `omega` |
| `BitVec` with `+ - < ≤`, `.toNat` | `bv_omega` |
| `BitVec` with bit ops, shifts, `if` | `bv_decide` (adds a native-code axiom) |
| has a definition to unfold | `simp [f]`, `unfold f` |
| `∀ x, …` / `A → B` | `intro x h` |
| `A ∧ B` | `constructor`, or `⟨pa, pb⟩` |
| `∃ x, P x` | `⟨witness, proof⟩`, `exists w` |
| `¬ ∀ x, P x` | `intro h; have := h bad; revert this; decide` |
| `if c then … else …` | `split`, `by_cases h : c` |
| about all lists / all `n` | `induction xs with …` (+ `generalizing acc`!) |
| hypothesis `h : A ∧ B` / `∃` | `obtain ⟨a, b⟩ := h` |
| exactly matches a fact | `exact h`, `assumption` |
| matches a lemma's conclusion | `apply lemma` |
| a machine run | `sym [prog, facts…]` (this repo) |

Combinators: `t <;> u` (u on every goal t made), `first | t | u`, `repeat t`,
`all_goals t`, `· t` (focus one goal).

## Machine-proof recipe (Stages 6–9)

1. `#eval trace prog [inputs…]`: know the shape and the step counts.
2. Loop head pc; invariant `structure` with fields: pc, each live register as a
   function of `i`, `ra`, `canRead`, (functional: accumulator, `mem`).
3. One iteration: gather facts (`inInput_of_lt`, `addr_succ_eq_iff`, `load_mem`,
   accumulator step) → `by_cases h : i + 1 = len` → `sym [...]` each side →
   new invariant with `constructor <;> sym [...]`.
4. All iterations: `induction k` on iterations left (copy `loop_all`).
5. Prologue / epilogue with `sym`, as `∃ m, run p N … = .running m ∧ …` lemmas.
6. Glue with `run_add_of_running`. Empty input separately.
7. `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.

Gotchas: state facts in simp-normal form (`input.tail`, `j + 1`,
`4294967295#32`); pass `input ≠ []`; give exit codes explicitly if `sym`
leaves `?m`; if `lake build` hangs but the editor didn't, checkpoint the state.

## Reading an audit

```
#print axioms foo
'foo' depends on axioms: [propext, Classical.choice, Quot.sound]   ← fine
'foo' depends on axioms: [..., sorryAx]                             ← unfinished
'foo' depends on axioms: [..., my_axiom]                            ← assumption, review it
'foo' depends on axioms: [..., foo._native.native_decide.ax_1_1]    ← trusts the compiler
```

## Lean ↔ Rocq

See `docs/10-rocq-and-the-real-thing.md`, Part 1.
