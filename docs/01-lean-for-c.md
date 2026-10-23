# 01 — Lean 4 for C programmers

*Time: 2–3 hours. Files: `Metal/S01_LeanForC.lean`, `Exercises/S01_LeanForC.lean`.*

## Why this stage exists

You can't state a theorem about code you can't write down. Lean is a
programming language first; the prover is built on top of it. This stage is
pure programming. No proofs.

## Why Lean (and not Rocq, Dafny, Isabelle…)

The article used **Rocq**. This course uses **Lean 4** for building and Rocq
for reading (Stage 10). Reasons:

* **One language for the machine and the proofs.** Our RISC-V model in Stage 5
  is ordinary Lean code. You can `#eval` it, single-step it, disassemble with
  it, *and* prove theorems about it, in the same file. In Rocq you'd write the
  model, then extract to OCaml to run it.
* **Tooling.** One install (`elan`), a fast language server, an infoview that
  shows the proof state as you move the cursor. That feedback loop matters
  more than anything else when learning.
* **Bit-vectors that work.** Lean's `BitVec` library plus `bv_omega`/`bv_decide`
  make machine arithmetic tractable out of the box (Stage 4).
* **Transfer.** Lean and Rocq are both dependent type theories with tactic
  languages; `intro`, `induction`, `simp`/`simpl`, `omega`/`lia` mean the same
  things. Stage 10 has the translation table.

Dafny, Verus, Frama-C and CBMC are excellent and closer to day-to-day
engineering; they hide the proof inside an SMT solver. That's great for using
verification, and bad for understanding what the article's 600k-line proofs
*are*. Stage 10 places them on the map.

## The mental model

| C | Lean | Notes |
|---|---|---|
| `int f(int a, int b)` | `def f (a b : Int) : Int` | Application is `f 1 2`, no parens/commas |
| `struct point { int x, y; }` | `structure Point where x : Int; y : Int` | `p.x`, and `{ p with x := 5 }` to "modify" |
| `enum` / tagged union | `inductive` | The compiler forbids reading the wrong variant |
| `switch` | `match` | Must be exhaustive, checked at compile time |
| `NULL`, `-1`, `errno` | `Option α`, `Except ε α` | Can't use the value without handling the error |
| `for`/`while` | recursion, `List.foldl` | Tail calls compile to loops |
| `uint32_t` | `UInt32` (fast) / `BitVec 32` (for proofs) | Both wrap mod 2^32 |
| `size_t` lengths in specs | `Nat` | Unbounded. `3 - 5 = 0`! |
| `const uint8_t *buf, size_t n` | `List (BitVec 8)` | No separate length to get wrong |

Three things will feel strange:

1. **Nothing mutates.** You never change a value; you build a new one. The
   compiler reuses memory in place when it can prove nobody else holds a
   reference, so it's less wasteful than it sounds.
2. **Every function terminates.** Lean must be able to see that recursion gets
   smaller. This isn't pedantry: if `def bogus : False := bogus` were allowed,
   you could "prove" anything, and the whole system would be worthless. To
   model a CPU that loops until `exit`, we'll pass **fuel** (a step budget).
   The article's models do too, in their own way.
3. **`Nat` is not `unsigned`.** `Nat` is the mathematical naturals: no
   overflow, and subtraction stops at 0. Specs are written in `Nat` precisely
   *because* there's no overflow to hide behind; code runs in `BitVec`. The
   gap between the two is where the bugs live, and Stage 4 is about it.

## Walk-through

Open `Metal/S01_LeanForC.lean` and put your cursor on each `#eval`. Sections:

1. **Values and functions.** Note `#eval` runs code at edit time.
2. **The numbers table.** Run every line. `(255 : UInt8) + 1` is 0, `255#8 + 1`
   is `0#8`, `(3 : Nat) - 5` is 0. Burn the last one into memory.
3. **`structure`.** `{ p with x := ... }` is your struct copy-and-modify.
4. **`inductive` and `match`.** Delete a case from `Shape.area` and read the error.
5. **`Option` / `Except`.** The type system enforces error checks.
6. **Recursion.** `sumList` (simple) and `sumAcc` (the tail-recursive loop you'd
   write in C). Stage 2 proves they agree on *every* list.
7. **Termination.** Why, and the fuel idea.
8. **Bytes.** `xs[i]?` returns `none` out of bounds; `xs[i]` *requires a proof*
   that `i < xs.length`. That's bounds-checking moved to compile time.
9. **The capstone harness as a spec.** `parseRecord` is the Stage 7 C harness's
   logic, written so that the off-by-one bug is impossible. The point: specs are
   written in this style, then *code* is proved to agree with them.
10. **`IO`.** Lean has a `do`-notation that looks imperative (`for`, `let mut`).
    It desugars to the recursion above.

## Exercises (`Exercises/S01_LeanForC.lean`)

| # | What | Skill |
|---|---|---|
| E1.1 ★ | XOR checksum | `foldl`, bit ops |
| E1.2 ★ | Count bytes matching a predicate | explicit recursion |
| E1.3 ★★ | Fletcher-16 | fold over a pair, `%` |
| E1.4 ★★ | Parse a decimal byte with overflow rejection | accumulator, `Option`, early exit |
| E1.5 ★★ | A stack machine where underflow = crash | `inductive`, `match` on two things — a preview of Stage 5 |
| E1.6 ★★ | The capstone harness as a spec | writing a reference implementation |

Tests are `#guard` lines, commented out; uncomment when you've implemented the
function. A failing `#guard` is a compile error showing the false expression.

## Common errors and what they mean

* **`failed to synthesize OfNat …`** — a numeric literal where Lean can't tell
  the type. Annotate: `(5 : UInt8)` or `5#8`.
* **`fail to show termination`** — your recursive call isn't on a smaller
  argument. Recurse on the tail of the list, or `n` from `n+1`.
* **`missing cases`** — your `match` isn't exhaustive. Good; that's the point.
* **Red squiggle on `#eval` with `sorry`** — Lean refuses to run code containing
  holes.

## Check yourself

1. Why does Lean insist every function terminates? What would go wrong in a
   *prover* if it didn't?
2. `(BitVec.ofNat 8 300).toNat` is 44. Why? Which C expression behaves the same?
3. You write the spec `remaining - used` in `Nat`, and the code computes it in
   `uint32_t`. When do they disagree?
4. In what sense does `xs[i]` (no `?`) "move a bounds check to compile time"?

Next: **[02 — Statements are types, proofs are programs](02-proofs.md)**.
