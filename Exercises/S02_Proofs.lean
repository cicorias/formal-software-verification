import Metal.S02_Proofs

/-!
# Exercises — Stage 2: proofs

Replace every `sorry` with a proof. Keep the statements exactly as they are
(changing the statement is how you "prove" the wrong thing: Stage 8).
Put your cursor inside a `by` block and watch the goal view.

Check: `lake build Exercises.S02_Proofs` — done when there are no `sorry` warnings.
-/

namespace Metal.S02.Ex
open Metal.S02

/-! ## E2.1 ★  Hint: both sides compute to the same number. -/
theorem e2_1 : 6 * 7 = 42 := sorry

/-! ## E2.2 ★  Hint: there are only 256 bytes. Check them all. -/
theorem e2_2 : ∀ x : BitVec 8, x &&& x = x := by
  sorry

/-! ## E2.3 ★  Hint: `intro` the variables and hypotheses, then one decision procedure. -/
theorem e2_3 : ∀ i len size : Nat, i < len → len ≤ size → i + 1 ≤ size := by
  sorry

/-- This is the fact that makes a `for (i = 0; i < n; i++)` loop terminate:
    `n - i` goes down each iteration. -/
theorem e2_3b (i n : Nat) (h : i < n) : n - (i + 1) < n - i := by
  sorry

/-! ## E2.4 ★  Find a byte x with x + x = 2 that isn't 1. (Wraparound is your friend.)
Give the witness with `⟨value, proof⟩`; the proof about concrete bytes is `by decide`. -/
theorem e2_4 : ∃ x : BitVec 8, x + x = 2 ∧ x ≠ 1 := sorry

/-! ## E2.5 ★  "Doubling never makes a byte smaller" — false. Find the input.
Pattern: `intro h`, specialize `h` to your counterexample, then `revert this; decide`
(see `S02_Proofs.lean` §3). -/
theorem e2_5 : ¬ ∀ x : BitVec 8, x * 2 ≥ x := by
  sorry

/-! ## E2.6 ★  No tactics needed: a proof of an implication is a function.
Write `fun hpq hqr hp => ...`. -/
theorem e2_6 (p q r : Prop) : (p → q) → (q → r) → p → r := sorry

/-! ## E2.7 ★★  Induction on `xs`. Template:
```
  induction xs with
  | nil => simp [len]
  | cons x xs ih => ...
```
-/
def len {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => 1 + len xs

theorem e2_7 {α : Type} (xs ys : List α) : len (xs ++ ys) = len xs + len ys := by
  sorry

/-! ## E2.8 ★★  Induction on `n`. You'll want `List.replicate_succ` and some arithmetic. -/
theorem e2_8 (n k : Nat) : sumList (List.replicate n k) = n * k := by
  sorry

/-! ## E2.9 ★★  Reverse with an accumulator.
The direct statement `revAcc [] xs = xs.reverse` does NOT go through by
induction (try it, and look at the stuck goal). First prove the general
version for every `acc` (`induction xs generalizing acc`), then use it. -/
def revAcc {α : Type} : List α → List α → List α
  | acc, []      => acc
  | acc, x :: xs => revAcc (x :: acc) xs

theorem revAcc_eq {α : Type} (acc xs : List α) : revAcc acc xs = xs.reverse ++ acc := by
  sorry

theorem e2_9 {α : Type} (xs : List α) : revAcc [] xs = xs.reverse := by
  sorry

/-! ## E2.10 ★★  Differential testing, as a proof: the tail-recursive counter
(what you'd write in C) agrees with the obvious one on every list.
Same strategy as E2.9. In the `cons` case, `split` the `if` and finish with `omega`. -/
def countZ : List Nat → Nat
  | []      => 0
  | x :: xs => (if x = 0 then 1 else 0) + countZ xs

def countZAcc (acc : Nat) : List Nat → Nat
  | []      => acc
  | x :: xs => countZAcc (if x = 0 then acc + 1 else acc) xs

theorem countZAcc_eq (acc : Nat) (xs : List Nat) : countZAcc acc xs = acc + countZ xs := by
  sorry

theorem e2_10 (xs : List Nat) : countZAcc 0 xs = countZ xs := by
  sorry

/-! ## E2.11 ★★  Idempotence (a spec shape you'll meet again in Stage 3).
`unfold clamp`, then split every `if` and let `omega` handle each case.
`repeat (first | omega | split)` is a handy combinator. -/
theorem e2_11 (lo hi x : Nat) (h : lo ≤ hi) : clamp lo hi (clamp lo hi x) = clamp lo hi x := by
  sorry

end Metal.S02.Ex
