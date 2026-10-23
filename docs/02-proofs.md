# 02 — Statements are types, proofs are programs

*Time: 4–6 hours. Files: `Metal/S02_Proofs.lean`, `Exercises/S02_Proofs.lean`.*

## The one idea

> A **theorem** is a definition whose *type* is a statement.
> A **proof** is a *value* of that type.
> **Checking** the proof is *type-checking* it.

```lean
theorem two_plus_two : 2 + 2 = 4 := rfl
--      ^ name          ^ the type     ^ the value (a proof)
```

The kernel that type-checks this is a few thousand lines of carefully reviewed
code. Producing the value can be arbitrarily hard; checking it is mechanical.
Everything in the article rests on that asymmetry.

You don't need to understand *why* "propositions are types" works (it's called
the Curry–Howard correspondence) to use it. Just treat a goal as a type you
have to construct a value of, and tactics as tools that build the value for you.

## The goal view is your debugger

Inside a `by` block, the infoview shows the **proof state**:

```
i n size : Nat          ← variables in scope
h1 : i < n              ← hypotheses (facts you have)
h2 : n ≤ size
⊢ i < size              ← the goal (what you must prove)
```

Each tactic transforms this state, like stepping in gdb. Put your cursor at the
end of each tactic line and watch. When a proof fails, the error shows the
state where you got stuck. **Read it every time.** It is the most precise bug
report you'll ever get, about your proof, your spec, or your code.

## Tactics you'll actually use

| Tactic | What it does | When |
|---|---|---|
| `rfl` | Both sides compute to the same thing | Concrete computations |
| `decide` / `decide +kernel` | Evaluate a finite question to `true` | Small finite domains (all 256 bytes) |
| `omega` | Complete decision procedure for linear `Nat`/`Int` arithmetic | Indices, bounds, `i + 1 ≤ n` |
| `simp [f, h]` | Rewrite with equations (unfold `f`, use `h`) until stuck | Most of the work, everywhere |
| `intro x h` | Move `∀ x` / `A →` from the goal into the context | Start of most proofs |
| `exact e` | "The proof is `e`" | When you have exactly the right fact |
| `apply f` | Reduce the goal to `f`'s hypotheses | Backward reasoning |
| `cases h` / `rcases`/`obtain ⟨a, b⟩ := h` | Take apart an `∧`, `∃`, `∨`, or inductive | Using hypotheses |
| `induction xs with …` | Prove for `[]` and for `x :: xs` given `xs` | Anything about all lists / all `n` |
| `by_cases h : P` | Split into `P` and `¬P` | Branches in code |
| `split` | Split on the `if`/`match` in the goal | Same |
| `have h : P := by …` | Prove an intermediate fact | Like a local checked `assert` |
| `constructor` / `⟨_, _⟩` | Build an `∧` or structure | Invariants with several fields |

Logic, as data structures you build and take apart:

* `P ∧ Q` is a pair. Build `⟨hp, hq⟩`; use `h.1`, `h.2`.
* `P ∨ Q` is a tagged union. Build `.inl hp`; use `cases h`.
* `∃ x, P x` is a pair of a witness and a proof. Build `⟨42, proof⟩`.
* `P → Q` is a function from proofs of `P` to proofs of `Q`.
* `¬ P` is `P → False`. **A counterexample is a proof of a negation**: to show
  `¬ ∀ x, P x`, assume the `∀`, apply it to your bad `x`, derive `False`.

## `decide` is exhaustive fuzzing

```lean
theorem xor_self_all_bytes : ∀ x : BitVec 8, x ^^^ x = 0 := by decide +kernel
```
That checks all 256 bytes. 6-bit pairs (4,096 cases) are fine too. This is a
real proof, and exactly as strong as fuzzing *every* input. It stops working
around 2^20 cases, which is why the article needs the next idea.

## Induction is the loop-invariant argument, formalised

To prove something for every list, prove it for `[]`, then show that if it
holds for `xs` it holds for `x :: xs`. That covers every list, just as "true on
loop entry, preserved by each iteration" covers every iteration count.

Walk through `sumList_append` in the lesson file, cursor on each line.

## The most important trick in this course: strengthen what you prove

The tail-recursive sum `sumAcc 0 xs` (what you'd write in C) should equal the
simple `sumList xs`. Try the obvious induction (it's in a comment in the lesson
file) and you get stuck:

```
⊢ sumAcc x xs = x + sumList xs        -- the goal after one step
ih : sumAcc 0 xs = sumList xs         -- what induction gave you
```

The accumulator isn't 0 any more, so the induction hypothesis doesn't apply.
The fix is to prove a **more general** statement, for every starting
accumulator:

```lean
theorem sumAcc_eq (acc : Nat) (xs : List Nat) : sumAcc acc xs = acc + sumList xs
```

and do `induction xs generalizing acc`. Now the hypothesis works for any `acc`,
including `acc + x`. The original statement is the special case `acc = 0`.

This is *exactly* writing a loop invariant that mentions the loop's running
state: "`acc + sum(rest)` equals the final answer" holds at every iteration,
while "`acc` is the answer" holds only at the end. You'll do this again for
the RLE encoder (Stage 3) and for every machine-code loop (Stages 6–8). If
you take one technique from this stage, take this one.

## Exercises (`Exercises/S02_Proofs.lean`)

| # | What | Main tactic |
|---|---|---|
| E2.1–2.3 ★ | Computation, exhaustive check, bounds arithmetic | `rfl`, `decide +kernel`, `omega` |
| E2.4–2.5 ★ | A witness; a counterexample | `⟨w, proof⟩`, `intro h; have := h x; …` |
| E2.6 ★ | Logic as functions | `fun` |
| E2.7–2.8 ★★ | Induction on lists and naturals | `induction`, `simp`, `omega` |
| E2.9–2.10 ★★ | **Generalise the hypothesis** (reverse, counting) | `induction … generalizing acc` |
| E2.11 ★★ | Idempotence of `clamp` | `split`, `repeat` |

## When you're stuck

1. Read the goal. What's the *shape*? An `=`, a `≤`, a `∀`, an `∃`, an `if`?
2. Is it arithmetic? Try `omega`. Is it about a concrete small value? `decide`.
3. Is there a definition to unfold? `simp [thatDef]` or `unfold thatDef`.
4. Is there an `if`? `split` or `by_cases`.
5. Is it about all lists/naturals? `induction`, and ask: does my hypothesis
   need to be more general?
6. Still stuck: `sorry` it, move on, come back. (`sorry` lets the rest of the
   file check.)

## Check yourself

1. In your own words: why is it safe to let an untrusted program (or an LLM)
   write proofs, but not to let it write the statement?
2. Why did the naive `sumAcc 0 xs = sumList xs` induction fail? What's the C
   analogy?
3. What is `decide` doing, and why doesn't it scale to the article's problem?
4. You proved `¬ ∀ x : BitVec 8, x * 2 ≥ x`. What exactly is the proof object?

Next: **[03 — Specifications](03-specs.md)**.
