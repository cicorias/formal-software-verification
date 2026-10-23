/-!
# Stage 2 — Statements are types, proofs are programs

The one idea of this stage:

> A **theorem** is a definition whose *type* is a statement.
> A **proof** is a *value* of that type.
> **Checking** a proof is type-checking it. That's the kernel's only job.

You already trust a type checker: when `gcc` accepts `int *p = &x;` it has
checked a (very boring) theorem. Lean's types are expressive enough to say
"this loop never reads past the buffer", and its checker is small enough to
trust (a few thousand lines). Finding the value of the type — the proof — can
be arbitrarily hard. Checking it is mechanical. That asymmetry is why it's
fine for an LLM to write proofs: we don't trust the writer, we trust the checker.

Read `docs/02-proofs.md` first. Then step through this file with your cursor,
watching the **goal view** in the infoview. The goal view is your debugger:
hypotheses above the line, what's left to prove (`⊢ ...`) below it.
-/

namespace Metal.S02

/-! ## 1. Proof by computation: `rfl` and `decide` -/

/-- `rfl` = "both sides compute to the same value". The kernel evaluates them. -/
theorem two_plus_two : 2 + 2 = 4 := rfl

theorem wraps : (255#8) + 1 = 0#8 := rfl

/-- `decide` = "this is a finite question; evaluate it to `true`".
    Here: check all 256 bytes. **This is exhaustive fuzzing.** It's a perfectly
    good proof when the input space is small. (`+kernel` asks the kernel to do
    the evaluation directly — slower to start, but no size limits.) -/
theorem xor_self_all_bytes : ∀ x : BitVec 8, x ^^^ x = 0 := by decide +kernel

/-- Two bytes = 65,536 cases. Still fine. Four bytes would be 4 billion; a
    64 MiB input is 256^67108864. That's why the article needs *proofs*:
    beyond tiny domains, enumeration is hopeless, and fuzzing samples a
    vanishing fraction. -/
theorem add_comm_6bit : ∀ x y : BitVec 6, x + y = y + x := by decide +kernel

/-! ## 2. Tactics: building a proof step by step

`by` switches into *tactic mode*. Each tactic transforms the goal. Put your
cursor after each line and watch the goal change. -/

/-- `intro` = "let n and h be arbitrary": moves `∀`/`→` into hypotheses.
    `omega` = a complete decision procedure for linear arithmetic on `Nat`/`Int`.
    It is your workhorse for index and bounds reasoning: it will never get
    `i + 1 ≤ n` wrong. -/
theorem idx_safe : ∀ i n size : Nat, i < n → n ≤ size → i < size := by
  intro i n size h1 h2
  omega

/-- Nat subtraction truncates at zero, and `omega` knows it. -/
theorem nat_sub_gotcha (a b : Nat) (h : a < b) : a - b = 0 := by omega

/-! ## 3. Logic you'll use: `∧`, `∨`, `∃`, `¬`

Proofs of these are data structures you build and take apart:
* `p ∧ q` is a pair: build with `⟨hp, hq⟩`, take apart with `h.1`, `h.2`.
* `p ∨ q` is a tagged union: build with `.inl hp`/`.inr hq`, take apart with `cases`.
* `∃ x, P x` is a pair (witness, proof): build with `⟨w, proof⟩`.
* `¬ p` means `p → False`: a function that turns a proof of `p` into absurdity. -/

example : ∃ n : Nat, n * n = 49 := ⟨7, rfl⟩

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

example (p q : Prop) (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩

example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero   => exact .inl rfl     -- `exact e` = "the proof is e"
  | succ k => exact .inr (by omega)

/-- To prove "not every x has property P", give one x that doesn't.
    A counterexample *is* a proof. (Stage 7 does this to a buggy binary.) -/
example : ¬ ∀ x : BitVec 8, x + 1 > x := by
  intro h
  have := h 255                  -- specialise the claim to x = 255
  revert this; decide            -- 255 + 1 = 0, and 0 > 255 is false

/-! ## 4. Induction: proofs about all lists

`decide` can't check infinitely many lists. Induction can: prove it for `[]`,
then prove "if it holds for `xs`, it holds for `x :: xs`". That covers every
list, the same way a loop that's correct on entry and preserves its invariant
is correct on exit. -/

def sumList : List Nat → Nat
  | []      => 0
  | x :: xs => x + sumList xs

theorem sumList_append (xs ys : List Nat) :
    sumList (xs ++ ys) = sumList xs + sumList ys := by
  induction xs with
  | nil => simp [sumList]                     -- [] ++ ys = ys; 0 + s = s
  | cons x xs ih =>                           -- ih : sumList (xs ++ ys) = sumList xs + sumList ys
    simp [sumList, ih]                        -- unfold one step, use ih…
    omega                                     -- …and finish the arithmetic

/-! `simp` rewrites with equations until it can't. `simp [f]` also unfolds
the definition of `f`. `simp [h]` also rewrites with hypothesis `h`.
`simp` is the tactic that does most of the work in this course — Stage 6's
symbolic execution is one big `simp` call. -/

/-! ## 5. The most important trick: strengthen what you prove

The tail-recursive sum (Stage 1) is what you'd write in C. Is it equal to the
simple one? Try the obvious statement: -/

def sumAcc (acc : Nat) : List Nat → Nat
  | []      => acc
  | x :: xs => sumAcc (acc + x) xs

/-
theorem sumAcc_eq_naive (xs : List Nat) : sumAcc 0 xs = sumList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [sumAcc, sumList]
    -- STUCK. Goal:   sumAcc x xs = x + sumList xs
    -- but ih says:   sumAcc 0 xs = sumList xs
    -- The accumulator isn't 0 any more! The induction hypothesis is too weak.
-/

/-- Fix: prove the statement for *every* starting accumulator. This is
    "generalize the induction hypothesis", and it is the same move as
    writing a loop invariant that mentions the loop's running state:
    `acc + sumList rest == the final answer` holds at every iteration. -/
theorem sumAcc_eq (acc : Nat) (xs : List Nat) : sumAcc acc xs = acc + sumList xs := by
  induction xs generalizing acc with      -- `generalizing acc`: ih works for ANY acc
  | nil => simp [sumAcc, sumList]
  | cons x xs ih =>
    simp [sumAcc, sumList, ih]            -- ih is used at acc := acc + x
    omega

/-- The statement we wanted is now a one-liner. The optimized version and the
    obviously-correct version agree on *every* list: differential testing,
    turned into a proof. -/
theorem sumAcc_correct (xs : List Nat) : sumAcc 0 xs = sumList xs := by
  simp [sumAcc_eq]

/-! ## 6. Case splits: `by_cases`, `split`, `cases` -/

def clamp (lo hi x : Nat) : Nat := if x < lo then lo else if x > hi then hi else x

theorem clamp_in_range (lo hi x : Nat) (h : lo ≤ hi) : lo ≤ clamp lo hi x ∧ clamp lo hi x ≤ hi := by
  unfold clamp
  split                                   -- one goal per branch of the first `if`
  · omega
  · split <;> omega                       -- `t <;> u`: run u on every goal t produced

/-! ## 7. `have`: intermediate facts, like local `assert`s that are checked -/

theorem triple (n : Nat) (h : n < 10) : 3 * n < 30 := by
  have h2 : 3 * n < 3 * 10 := by omega
  simpa using h2                          -- `simpa`: simplify h2 and the goal, then match

/-! ## 8. What you must remember

* `sorry` proves anything. It's a hole, not a proof. Lean warns
  "declaration uses `sorry`" and `#print axioms` lists `sorryAx`.
* If a tactic fails, the error shows the goal it couldn't close. Read it:
  it is a precise bug report — about your proof, your spec, or your code.
* Tactic cheat-sheet (`docs/02-proofs.md` has the full table):
  `rfl decide omega simp intro exact apply cases induction by_cases split have constructor`
-/

end Metal.S02
