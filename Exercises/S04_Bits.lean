import Metal.S04_Bits

/-!
# Exercises — Stage 4: true or false?

Each `E4.n` below states a claim about 32-bit (or 8-bit) words. **Some are
false.** For each one:

1. Predict: true or false? (Write it down. Be honest.)
2. Ask the machine: replace `sorry` with `intro ...; bv_decide` (or
   `bv_omega` for `.toNat` claims). If it's false, `bv_decide` prints a
   counterexample.
3. If it's TRUE: keep the proof.
   If it's FALSE: put `¬` in front of the statement (wrap the `∀ ...` in
   parentheses: `¬ (∀ x : Word, ...)` — or just `¬ ∀ x : Word, ...`) and prove
   *that*, using the counterexample:
   ```
   intro h; have := h 0x80000000; revert this; decide
   ```
   This is the only exercise set where you're allowed to change a statement,
   and only by adding `¬`.

Tactic guide: `bv_decide` for anything with `&&& ||| ^^^ <<< >>>`, `slt`,
`if`; `bv_omega` for `+ - ≤ <` and `.toNat`. Some need `simp at h` first to
turn a `Bool` hypothesis (`... = true`) into a `Prop`.
-/

namespace Metal.S04.Ex
open Metal.S04

/-! ## E4.1 Subtraction undoes addition, even with wraparound. -/
theorem e4_1 : ∀ x y : Word, x + y - y = x := by
  sorry

/-! ## E4.2 Shift left then right gives back the original. -/
theorem e4_2 : ∀ x : Word, (x <<< 1) >>> 1 = x := by
  sorry

/-! ## E4.3 `x & -x` (isolate lowest set bit) is nonzero when x is. -/
theorem e4_3 : ∀ x : Word, x ≠ 0 → x &&& (0 - x) ≠ 0 := by
  sorry

/-! ## E4.4 If a < b (unsigned), then a + 1 ≤ b. -/
theorem e4_4 : ∀ a b : Word, a < b → a + 1 ≤ b := by
  sorry

/-! ## E4.5 If a < b *signed*, then a + 1 ≤ b (unsigned).
(Code that checks with one signedness and indexes with the other.) -/
theorem e4_5 : ∀ a b : Word, a.slt b → a + 1 ≤ b := by
  sorry

/-! ## E4.6 Doubling a value ≤ 0x7FFFFFFF doesn't overflow. -/
theorem e4_6 : ∀ n : Word, n ≤ 0x7FFFFFFF → (n + n).toNat = 2 * n.toNat := by
  sorry

/-! ## E4.7 Another bounds check: `off <= size && len <= size - off`. Sound? -/
theorem e4_7 : ∀ off len size : Word,
    (off ≤ size && len ≤ size - off) = true → off.toNat + len.toNat ≤ size.toNat := by
  sorry

/-! ## E4.8 Sign-extending a byte to 32 bits preserves its unsigned value. -/
theorem e4_8 : ∀ x : BitVec 8, (x.signExtend 32).toNat = x.toNat := by
  sorry

/-! ## E4.9 Rounding up to a multiple of 4 never goes down.
(`(x + 3) & ~3` is in every allocator you've ever read.) -/
theorem e4_9 : ∀ x : Word, ((x + 3) &&& ~~~3) ≥ x := by
  sorry

/-! ## E4.10 Rounding up an already-aligned value is a no-op. -/
theorem e4_10 : ∀ x : Word, x &&& 3 = 0 → ((x + 3) &&& ~~~3) = x := by
  sorry

/-! ## E4.11 ★★★ Fix E4.9 with a type, and give it a spec.
Write `alignUp4` so it returns `none` exactly when rounding up would wrap.
Then prove: the result is aligned, not below `x`, and less than 4 above it;
and it returns `some` whenever `x ≤ 0xFFFFFFFC`.
Hints: `unfold alignUp4 at h`, `split at h`, `cases h`, then `bv_decide`. -/
def alignUp4 (x : Word) : Option Word := sorry

theorem alignUp4_spec (x y : Word) (h : alignUp4 x = some y) :
    y &&& 3 = 0 ∧ x ≤ y ∧ y - x < 4 := by
  sorry

theorem alignUp4_total (x : Word) (hx : x ≤ 0xFFFFFFFC) : (alignUp4 x).isSome := by
  sorry

end Metal.S04.Ex
