import Metal.S04_Bits

/-! # Solutions — Stage 4

Verdicts: TRUE: 1, 3, 4, 6, 7, 10.  FALSE: 2, 5, 8, 9. -/

namespace Metal.S04.Ex
open Metal.S04

/-! ## E4.1 TRUE — subtraction undoes addition, even with wraparound -/
theorem e4_1 : ∀ x y : Word, x + y - y = x := by
  intro x y; bv_omega

/-! ## E4.2 FALSE — the top bit falls off -/
theorem e4_2 : ¬ ∀ x : Word, (x <<< 1) >>> 1 = x := by
  intro h; have := h 0x80000000; revert this; decide

/-! ## E4.3 TRUE — a nonzero word has a lowest set bit -/
theorem e4_3 : ∀ x : Word, x ≠ 0 → x &&& (0 - x) ≠ 0 := by
  intro x; bv_decide

/-! ## E4.4 TRUE — unsigned `<` leaves room for +1 -/
theorem e4_4 : ∀ a b : Word, a < b → a + 1 ≤ b := by
  intro a b; bv_omega

/-! ## E4.5 FALSE — mixing a signed compare with unsigned arithmetic.
a = -2 (0xFFFFFFFE) is signed-less-than 0, but a + 1 = 0xFFFFFFFF is not ≤ 0 unsigned. -/
theorem e4_5 : ¬ ∀ a b : Word, a.slt b → a + 1 ≤ b := by
  intro h; have := h 0xFFFFFFFE 0 (by decide); revert this; decide

/-! ## E4.6 TRUE — doubling a value below 2^31 doesn't overflow -/
theorem e4_6 : ∀ n : Word, n ≤ 0x7FFFFFFF → (n + n).toNat = 2 * n.toNat := by
  intro n h; bv_omega

/-! ## E4.7 TRUE — another correct bounds check (subtract the side you've checked) -/
theorem e4_7 : ∀ off len size : Word,
    (off ≤ size && len ≤ size - off) = true → off.toNat + len.toNat ≤ size.toNat := by
  intro off len size h; simp at h; bv_omega

/-! ## E4.8 FALSE — sign extension changes the unsigned value of 0x80..0xFF -/
theorem e4_8 : ¬ ∀ x : BitVec 8, (x.signExtend 32).toNat = x.toNat := by
  intro h; have := h 0x80; revert this; decide

/-! ## E4.9 FALSE — round-up-to-4 overflows near the top of the address space -/
theorem e4_9 : ¬ ∀ x : Word, ((x + 3) &&& ~~~3) ≥ x := by
  intro h; have := h 0xFFFFFFFD; revert this; decide

/-! ## E4.10 TRUE — rounding an aligned value up is a no-op -/
theorem e4_10 : ∀ x : Word, x &&& 3 = 0 → ((x + 3) &&& ~~~3) = x := by
  intro x; bv_decide

/-! ## E4.11 ★★★ A safe `alignUp4` with a spec -/
def alignUp4 (x : Word) : Option Word :=
  if x ≤ 0xFFFFFFFC then some ((x + 3) &&& ~~~3) else none

theorem alignUp4_spec (x y : Word) (h : alignUp4 x = some y) :
    y &&& 3 = 0 ∧ x ≤ y ∧ y - x < 4 := by
  unfold alignUp4 at h
  split at h
  · cases h; bv_decide
  · cases h

theorem alignUp4_total (x : Word) (hx : x ≤ 0xFFFFFFFC) : (alignUp4 x).isSome := by
  unfold alignUp4
  split
  · rfl
  · contradiction

end Metal.S04.Ex
