import Metal.S03_Specs

/-!
# Exercises — Stage 3: specifications

Some of these ask you to *write* a spec, not just prove one. The point of
the stage: the statement is the part you're responsible for.

Check: `lake build Exercises.S03_Specs`.
-/

namespace Metal.S03.Ex
open Metal.S03

/-! ## E3.1 ★★ An output-size bound
A decompression-bomb / DoS-style property: the encoder never more than
doubles its input. As usual, the statement about `encode` is too weak for
induction; prove a statement about `encodeRun` first. Its shape is given.
Hints: `induction xs generalizing cur cnt`; in the `cons` case, `unfold encodeRun`
and `split`; get the IH at the right arguments with `have := ih cur (cnt + 1)`;
`simp` then `omega`. -/
theorem encodeRun_length (cur : Byte) (cnt : Nat) (xs : List Byte) :
    (encodeRun cur cnt xs).length ≤ 2 * (xs.length + 1) := by
  sorry

theorem e3_1 (xs : List Byte) : (encode xs).length ≤ 2 * xs.length := by
  sorry

/-! ## E3.2 ★ The buggy encoder violates the roundtrip spec.
One line, using a theorem from the lesson. -/
theorem e3_2 : ¬ ∀ xs : List Byte, decode (encodeBuggy xs) = xs := by
  sorry

/-! ## E3.3 ★★ Write a spec that `encodeLazy` fails.
`encodeLazy` round-trips but never compresses. Define `CompressesRuns enc`:
"for every byte b and every 1 ≤ k ≤ 255, encoding k copies of b gives 2 bytes".
Then show the real encoder satisfies it (the lesson has a lemma that does
the heavy lifting) and the lazy one doesn't (find a k). -/
def CompressesRuns (enc : List Byte → List Byte) : Prop := sorry

theorem e3_3_real : CompressesRuns encode := by
  sorry

theorem e3_3_lazy : ¬ CompressesRuns encodeLazy := by
  sorry

/-! ## E3.4 ★★ Which property notices which mutation?
A *mutant* cuts runs at 254 instead of 255. Before proving anything, predict:
is it still a correct codec? Will the roundtrip property catch the mutation?
Will `CompressesRuns`? Then prove your predictions.
(The roundtrip proof is a copy of the lesson's, with one number changed.) -/
def encodeRunM (cur : Byte) (cnt : Nat) : List Byte → List Byte
  | []      => [BitVec.ofNat 8 cnt, cur]
  | x :: xs =>
    if x = cur ∧ cnt < 254 then encodeRunM cur (cnt + 1) xs
    else BitVec.ofNat 8 cnt :: cur :: encodeRunM x 1 xs

def encodeM : List Byte → List Byte
  | []      => []
  | x :: xs => encodeRunM x 1 xs

theorem e3_4_roundtrip_blind (xs : List Byte) : decode (encodeM xs) = xs := by
  sorry

theorem e3_4_compression_sees_it : ¬ CompressesRuns encodeM := by
  sorry

/-! ## E3.5 ★★★ Idempotence of adjacent-dedup
`dedupAdj` collapses runs: [1,1,2,2,2,1] ↦ [1,2,1]. Prove that doing it twice
is the same as doing it once. Suggested route (each is an induction):
1. the head of the list survives: `∃ t, dedupAdj (x :: xs) = x :: t`;
2. the output satisfies `NoAdjDup`;
3. on a `NoAdjDup` list, `dedupAdj` is the identity;
4. combine.
In the inductions you'll want `cases xs with | nil | cons y ys` to expose
two elements, and `unfold dedupAdj; split`. -/
def dedupAdj : List Nat → List Nat
  | []             => []
  | [x]            => [x]
  | x :: y :: rest => if x = y then dedupAdj (y :: rest) else x :: dedupAdj (y :: rest)

def NoAdjDup : List Nat → Prop
  | x :: y :: rest => x ≠ y ∧ NoAdjDup (y :: rest)
  | _              => True

theorem e3_5 (xs : List Nat) : dedupAdj (dedupAdj xs) = dedupAdj xs := by
  sorry

end Metal.S03.Ex
