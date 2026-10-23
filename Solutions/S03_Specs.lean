import Metal.S03_Specs

/-! # Solutions — Stage 3 -/

namespace Metal.S03.Ex
open Metal.S03

/-! ## E3.1 ★★ Output size bound (a DoS-style spec) -/
theorem encodeRun_length (cur : Byte) (cnt : Nat) (xs : List Byte) :
    (encodeRun cur cnt xs).length ≤ 2 * (xs.length + 1) := by
  induction xs generalizing cur cnt with
  | nil => simp [encodeRun]
  | cons x xs ih =>
    unfold encodeRun
    split
    · have := ih cur (cnt + 1); simp; omega
    · have := ih x 1; simp; omega

theorem e3_1 (xs : List Byte) : (encode xs).length ≤ 2 * xs.length := by
  cases xs with
  | nil => simp [encode]
  | cons x xs => have := encodeRun_length x 1 xs; simp [encode]; omega

/-! ## E3.2 ★ The buggy encoder violates the roundtrip spec -/
theorem e3_2 : ¬ ∀ xs : List Byte, decode (encodeBuggy xs) = xs := by
  intro h
  exact buggy_counterexample (h _)

/-! ## E3.3 ★★ A spec that rules out `encodeLazy` -/
def CompressesRuns (enc : List Byte → List Byte) : Prop :=
  ∀ (b : Byte) (k : Nat), 1 ≤ k → k ≤ 255 → (enc (List.replicate k b)).length = 2

theorem e3_3_real : CompressesRuns encode := by
  intro b k h1 h2
  simp [encode_run_small b k h1 h2]

theorem e3_3_lazy : ¬ CompressesRuns encodeLazy := by
  intro h
  have := h 0 2 (by omega) (by omega)
  revert this; decide

/-! ## E3.4 ★★ Which property notices which mutation?
The mutant cuts runs at 254 instead of 255. It's still a correct codec, just
slightly worse at compressing. Roundtrip can't see the difference; the
compression spec can. -/
def encodeRunM (cur : Byte) (cnt : Nat) : List Byte → List Byte
  | []      => [BitVec.ofNat 8 cnt, cur]
  | x :: xs =>
    if x = cur ∧ cnt < 254 then encodeRunM cur (cnt + 1) xs
    else BitVec.ofNat 8 cnt :: cur :: encodeRunM x 1 xs

def encodeM : List Byte → List Byte
  | []      => []
  | x :: xs => encodeRunM x 1 xs

theorem decode_encodeRunM (cur : Byte) (cnt : Nat) (xs : List Byte)
    (h1 : 1 ≤ cnt) (h2 : cnt ≤ 254) :
    decode (encodeRunM cur cnt xs) = List.replicate cnt cur ++ xs := by
  induction xs generalizing cur cnt with
  | nil => simp [encodeRunM, decode, toNat_ofNat_byte cnt (by omega)]
  | cons x xs ih =>
    unfold encodeRunM
    split
    · rename_i hx
      rw [ih cur (cnt + 1) (by omega) (by omega), hx.1]
      simp [List.replicate_succ']
    · simp [decode, toNat_ofNat_byte cnt (by omega), ih x 1 (by omega) (by omega)]

theorem e3_4_roundtrip_blind (xs : List Byte) : decode (encodeM xs) = xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [encodeM, decode_encodeRunM x 1 xs (by omega) (by omega)]

theorem e3_4_compression_sees_it : ¬ CompressesRuns encodeM := by
  intro h
  have := h 0 255 (by omega) (by omega)
  revert this; decide +kernel

/-! ## E3.5 ★★★ Idempotence of adjacent-dedup -/
def dedupAdj : List Nat → List Nat
  | []           => []
  | [x]          => [x]
  | x :: y :: rest => if x = y then dedupAdj (y :: rest) else x :: dedupAdj (y :: rest)

/-- "No two neighbours are equal." -/
def NoAdjDup : List Nat → Prop
  | x :: y :: rest => x ≠ y ∧ NoAdjDup (y :: rest)
  | _              => True

/-- The head survives deduplication. -/
theorem dedupAdj_cons_head (x : Nat) (xs : List Nat) : ∃ t, dedupAdj (x :: xs) = x :: t := by
  induction xs generalizing x with
  | nil => exact ⟨[], rfl⟩
  | cons y ys ih =>
    unfold dedupAdj
    split
    · rename_i h; subst h; exact ih x
    · exact ⟨_, rfl⟩

/-- Its output has no adjacent duplicates… -/
theorem dedupAdj_noAdjDup (xs : List Nat) : NoAdjDup (dedupAdj xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    cases xs with
    | nil => trivial
    | cons y ys =>
      unfold dedupAdj
      split
      · exact ih
      · rename_i hne
        obtain ⟨t, ht⟩ := dedupAdj_cons_head y ys
        rw [ht] at ih ⊢
        exact ⟨hne, ih⟩

/-- …and on such lists it does nothing. -/
theorem dedupAdj_of_noAdjDup (xs : List Nat) (h : NoAdjDup xs) : dedupAdj xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      obtain ⟨hne, hrest⟩ := h
      simp [dedupAdj, hne, ih hrest]

theorem e3_5 (xs : List Nat) : dedupAdj (dedupAdj xs) = dedupAdj xs :=
  dedupAdj_of_noAdjDup _ (dedupAdj_noAdjDup xs)

end Metal.S03.Ex
