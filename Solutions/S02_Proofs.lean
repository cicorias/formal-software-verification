import Metal.S02_Proofs

/-! # Solutions — Stage 2 -/

namespace Metal.S02.Ex
open Metal.S02

/-! ## E2.1 ★ -/
theorem e2_1 : 6 * 7 = 42 := rfl

/-! ## E2.2 ★ exhaustive check -/
theorem e2_2 : ∀ x : BitVec 8, x &&& x = x := by decide +kernel

/-! ## E2.3 ★ index arithmetic -/
theorem e2_3 : ∀ i len size : Nat, i < len → len ≤ size → i + 1 ≤ size := by
  intro i len size h1 h2; omega

/-- The loop variant goes down. -/
theorem e2_3b (i n : Nat) (h : i < n) : n - (i + 1) < n - i := by omega

/-! ## E2.4 ★ a witness: 0x81 + 0x81 = 0x102, which wraps to 2 -/
theorem e2_4 : ∃ x : BitVec 8, x + x = 2 ∧ x ≠ 1 := ⟨0x81, by decide⟩

/-! ## E2.5 ★ a counterexample: 128 * 2 wraps to 0 -/
theorem e2_5 : ¬ ∀ x : BitVec 8, x * 2 ≥ x := by
  intro h
  have := h 128
  revert this; decide

/-! ## E2.6 ★ plain logic: a proof is a function -/
theorem e2_6 (p q r : Prop) : (p → q) → (q → r) → p → r :=
  fun hpq hqr hp => hqr (hpq hp)

/-! ## E2.7 ★★ induction -/
def len {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => 1 + len xs

theorem e2_7 {α : Type} (xs ys : List α) : len (xs ++ ys) = len xs + len ys := by
  induction xs with
  | nil => simp [len]
  | cons x xs ih => simp [len, ih]; omega

/-! ## E2.8 ★★ -/
theorem e2_8 (n k : Nat) : sumList (List.replicate n k) = n * k := by
  induction n with
  | zero => simp [sumList]
  | succ n ih => simp [List.replicate_succ, sumList, ih, Nat.succ_mul]; omega

/-! ## E2.9 ★★ reverse with an accumulator: generalize! -/
def revAcc {α : Type} : List α → List α → List α
  | acc, []      => acc
  | acc, x :: xs => revAcc (x :: acc) xs

theorem revAcc_eq {α : Type} (acc xs : List α) : revAcc acc xs = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp [revAcc]
  | cons x xs ih => simp [revAcc, ih]

theorem e2_9 {α : Type} (xs : List α) : revAcc [] xs = xs.reverse := by
  simp [revAcc_eq]

/-! ## E2.10 ★★ differential: the loop and the spec agree -/
def countZ : List Nat → Nat
  | []      => 0
  | x :: xs => (if x = 0 then 1 else 0) + countZ xs

def countZAcc (acc : Nat) : List Nat → Nat
  | []      => acc
  | x :: xs => countZAcc (if x = 0 then acc + 1 else acc) xs

theorem countZAcc_eq (acc : Nat) (xs : List Nat) : countZAcc acc xs = acc + countZ xs := by
  induction xs generalizing acc with
  | nil => simp [countZAcc, countZ]
  | cons x xs ih =>
    simp only [countZAcc, countZ, ih]
    split <;> omega

theorem e2_10 (xs : List Nat) : countZAcc 0 xs = countZ xs := by
  simp [countZAcc_eq]

/-! ## E2.11 ★★ idempotence of `clamp` -/
theorem e2_11 (lo hi x : Nat) (h : lo ≤ hi) : clamp lo hi (clamp lo hi x) = clamp lo hi x := by
  unfold clamp
  -- `repeat` keeps splitting `if`s until none are left; then arithmetic.
  repeat (first | omega | split)

end Metal.S02.Ex
