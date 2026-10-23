/-!
# Stage 3 — Specifications: saying what "correct" means

A proof shows that code meets a spec. It says nothing about whether the spec
is the one you wanted. In the article, *every* theorem is "this fuzz target
doesn't crash", and fuzz targets already encode properties as checks that
abort: round-trips, idempotence, differential tests. So this stage is about
the shapes those properties take, and how they go wrong.

The running example: a run-length encoder (RLE), the simplest compressor.
It mirrors the article's LZO example ("compress then decompress returns the
original"). Format: a list of `[count, value]` byte pairs.

    [7, 7, 7, 9]   ⇄   [3, 7,  1, 9]

Read `docs/03-specs.md` alongside.
-/

namespace Metal.S03

abbrev Byte := BitVec 8

/-! ## 1. The codec -/

/-- Decode: expand each `[n, b]` pair into `n` copies of `b`. A trailing odd
    byte is ignored (decoders must decide what to do with junk). -/
def decode : List Byte → List Byte
  | n :: b :: rest => List.replicate n.toNat b ++ decode rest
  | _              => []

/-- Encode helper: we're in a run of `cnt` copies of `cur`. A count must fit
    in a byte, so a run is cut at 255. -/
def encodeRun (cur : Byte) (cnt : Nat) : List Byte → List Byte
  | []      => [BitVec.ofNat 8 cnt, cur]
  | x :: xs =>
    if x = cur ∧ cnt < 255 then encodeRun cur (cnt + 1) xs
    else BitVec.ofNat 8 cnt :: cur :: encodeRun x 1 xs

def encode : List Byte → List Byte
  | []      => []
  | x :: xs => encodeRun x 1 xs

#eval encode [7, 7, 7, 9]              -- [3, 7, 1, 9]
#eval decode (encode [7, 7, 7, 9])     -- [7, 7, 7, 9]

/-! ## 2. The same codec with a bug a fuzzer won't find

Someone "simplified" the run check and dropped `cnt < 255`. On a run of 256
equal bytes, the count wraps to 0 (`BitVec.ofNat 8 256 = 0`): 256 bytes vanish.
In C this is the classic `uint8_t count` overflow. -/

def encodeRunBuggy (cur : Byte) (cnt : Nat) : List Byte → List Byte
  | []      => [BitVec.ofNat 8 cnt, cur]
  | x :: xs =>
    if x = cur then encodeRunBuggy cur (cnt + 1) xs
    else BitVec.ofNat 8 cnt :: cur :: encodeRunBuggy x 1 xs

def encodeBuggy : List Byte → List Byte
  | []      => []
  | x :: xs => encodeRunBuggy x 1 xs

/-! ## 3. Fuzz it

A tiny property-based tester: random inputs, check `decode (encode x) = x`.
Run it (cursor on the `#eval`). The buggy encoder passes thousands of tests:
a random input essentially never contains 256 equal bytes in a row. This is
the article's point about the decompressor bug that "needed a ~20 MB input
with one rare layout": the bug lives where random sampling doesn't go. -/

/-- Random byte list: length up to `maxLen`, bytes drawn from `0..alphabet-1`
    (a small alphabet makes runs *more* likely: we're trying to help the fuzzer). -/
def randomInput (maxLen alphabet : Nat) : IO (List Byte) := do
  let len ← IO.rand 0 maxLen
  let mut xs : List Byte := []
  for _ in [0:len] do
    xs := BitVec.ofNat 8 (← IO.rand 0 (alphabet - 1)) :: xs
  return xs

/-- Run `trials` random tests of `prop`; report the first failure. -/
def fuzz (name : String) (prop : List Byte → Bool) (trials maxLen alphabet : Nat) : IO Unit := do
  for i in [0:trials] do
    let x ← randomInput maxLen alphabet
    unless prop x do
      IO.println s!"{name}: FAILED on trial {i}, input length {x.length}"
      return
  IO.println s!"{name}: passed {trials} random tests"

#eval fuzz "roundtrip (buggy)" (fun x => decode (encodeBuggy x) == x) 2000 600 4
#eval fuzz "roundtrip (fixed)" (fun x => decode (encode x) == x) 2000 600 4

/-! But the bug is real. One concrete input, checked by computation: -/
theorem buggy_counterexample :
    decode (encodeBuggy (List.replicate 256 7)) ≠ List.replicate 256 7 := by
  decide +kernel

/-! ## 4. Prove it

The roundtrip property for *all* inputs. As in Stage 2, the statement we
want (`decode (encode xs) = xs`) is too weak to prove by induction directly;
we strengthen it to talk about a run in progress: "if we're in a run of
`cnt` copies of `cur`, decoding the rest gives back those copies plus the
rest of the input". That's the loop invariant of the encoder. -/

/-- A count `≤ 255` survives the trip through a byte. **This** is where the
    proof needs `cnt < 255` in the `if`; without it, this lemma's hypothesis
    can't be established, and the proof attempt for the buggy encoder gets
    stuck exactly here — pointing at the bug. -/
theorem toNat_ofNat_byte (cnt : Nat) (h : cnt ≤ 255) : (BitVec.ofNat 8 cnt).toNat = cnt := by
  simp [BitVec.toNat_ofNat]; omega

theorem decode_encodeRun (cur : Byte) (cnt : Nat) (xs : List Byte)
    (h1 : 1 ≤ cnt) (h2 : cnt ≤ 255) :
    decode (encodeRun cur cnt xs) = List.replicate cnt cur ++ xs := by
  induction xs generalizing cur cnt with
  | nil =>
    simp [encodeRun, decode, toNat_ofNat_byte cnt h2]
  | cons x xs ih =>
    unfold encodeRun
    split
    · -- extend the run: x = cur and there's room
      rename_i hx
      rw [ih cur (cnt + 1) (by omega) (by omega), hx.1]
      simp [List.replicate_succ']
    · -- close the run and start a new one at x
      simp [decode, toNat_ofNat_byte cnt h2, ih x 1 (by omega) (by omega)]

/-- **Roundtrip.** For every input, of every length. -/
theorem decode_encode (xs : List Byte) : decode (encode xs) = xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [encode, decode_encodeRun x 1 xs (by omega) (by omega)]

/-! ## 5. A spec only says what it says

Roundtrip is necessary. It's not sufficient. This "codec" satisfies it: -/

def encodeLazy (xs : List Byte) : List Byte := xs.flatMap (fun b => [1, b])

theorem lazy_roundtrip (xs : List Byte) : decode (encodeLazy xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeLazy, decode] at *; exact ih

/-! It never compresses anything: every byte becomes two. A spec that only
says "roundtrip" can't tell it apart from a real compressor. If compression
matters, say so: e.g. "a run of k ≤ 255 equal bytes encodes to 2 bytes". -/

/-- Generalised (the encoder's invariant again): after reading `i` copies of
    `b`, with `j` more to come, the encoder emits exactly one pair. -/
theorem encodeRun_replicate (b : Byte) (j : Nat) :
    ∀ i, i + j ≤ 255 → 1 ≤ i → encodeRun b i (List.replicate j b) = [BitVec.ofNat 8 (i + j), b] := by
  induction j with
  | zero => intro i _ _; simp [encodeRun]
  | succ j ih =>
    intro i hij hi
    rw [List.replicate_succ]
    unfold encodeRun
    split
    · rw [ih (i + 1) (by omega) (by omega)]
      simp [Nat.add_assoc, Nat.add_comm 1 j]
    · rename_i h; exact absurd ⟨rfl, by omega⟩ h   -- the run can't end early

theorem encode_run_small (b : Byte) (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 255) :
    encode (List.replicate k b) = [BitVec.ofNat 8 k, b] := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [List.replicate_succ, encode, encodeRun_replicate b j 1 (by omega) (by omega), Nat.add_comm]

/-! ## 6. The catalogue of property shapes

All of these are just `Prop`s about functions. The article's fuzz targets use
every one of them (as `if (!cond) abort();`, which the no-crash theorem then
covers):

| Shape           | Lean statement                                  | Catches                           |
|-----------------|-------------------------------------------------|-----------------------------------|
| Round-trip      | `decode (encode x) = x`                          | lossy codecs, wrap-around counts  |
| Idempotence     | `norm (norm x) = norm x`                         | half-done normalisation           |
| Differential    | `fast x = reference x`                           | optimisation bugs (`sumAcc_eq`)   |
| Invariant       | `valid s → valid (op s)`                         | data-structure corruption         |
| Safety          | `(f x).isSome` / "never faults"                 | crashes, OOB, the article's spec  |
| Bound           | `(encode x).length ≤ 2 * x.length`               | blow-ups, DoS                     |
| Totality        | Lean functions are total by construction        | hangs (Stage 5: fuel)             |

And the rule from OSS Verify's checklist, which applies to every one of them:
**a property that no change to the code can make fail checks nothing.**
Mutate the code; make sure the property notices. (`lazy_roundtrip` above is
what happens when you skip that step.)
-/

end Metal.S03
