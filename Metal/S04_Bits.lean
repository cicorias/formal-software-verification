import Std.Tactic.BVDecide

/-!
# Stage 4 — Bits, bytes, and overflow

Home turf. Everything here is a bug you have shipped, seen shipped, or
reviewed at 2 a.m. The new thing is that we can now *settle* questions like
"can this addition overflow?" for all 2^64 input pairs at once, and when the
answer is "yes", get the input that does it.

Two decision procedures do the work:

* **`bv_omega`** — turns `BitVec` facts into facts about `.toNat` (with the
  `mod 2^n` made explicit) and runs `omega`. Good for `+ - < ≤` and
  constants. Fully checked by Lean's kernel.
* **`bv_decide`** — "bit-blasts" the goal to a SAT problem, runs the CaDiCaL
  SAT solver, and checks the solver's certificate. Handles everything:
  `&&& ||| ^^^ <<< >>>`, multiplication, `if`. When the claim is false, it
  prints a **counterexample**.

Trust note (see Stage 8): the SAT solver itself is not trusted; its answer
comes with an LRAT certificate that Lean checks. In this Lean version that
check runs as *compiled code*, so `#print axioms` shows an extra
`…_native.bv_decide…` axiom: you're trusting Lean's compiler too. `bv_omega`
and `decide +kernel` don't need that. The machine proofs in Stages 6–8 use
only `bv_omega`, on purpose.

Read `docs/04-bits.md` alongside.
-/

namespace Metal.S04

abbrev Word := BitVec 32

/-! ## 1. Reading BitVec

`5#8` is the 8-bit vector with value 5. `x.toNat` is its unsigned meaning,
`x.toInt` its two's-complement meaning. `<`/`≤` on `BitVec` are unsigned;
`x.slt y` is signed. -/

#eval (0xFF#8).toNat          -- 255
#eval (0xFF#8).toInt          -- -1
#eval (0xFF#8).signExtend 32  -- 0xffffffff#32   (what `(int32_t)(int8_t)0xFF` does)
#eval (0xFF#8).zeroExtend 32  -- 0x000000ff#32   (what `(uint32_t)(uint8_t)0xFF` does)
#eval (0x80000000#32) < 1     -- false (unsigned)
#eval (0x80000000#32).slt 1   -- true  (signed: it's INT_MIN)

/-! ## 2. The binary-search midpoint bug

`(lo + hi) / 2` overflows when `lo + hi ≥ 2^32` (famously in the JDK's
`binarySearch`, for nine years). The result can land *below* `lo`. -/

def midBuggy (lo hi : Word) : Word := (lo + hi) >>> 1
def midFixed (lo hi : Word) : Word := lo + ((hi - lo) >>> 1)

/-- The fix stays in range, for all 2^64 pairs. -/
theorem midFixed_in_range (lo hi : Word) (h : lo ≤ hi) :
    lo ≤ midFixed lo hi ∧ midFixed lo hi ≤ hi := by
  unfold midFixed; bv_decide

/-- And it computes the *mathematical* midpoint: the spec is in `Nat`,
    where there's no overflow to hide behind. -/
theorem midFixed_correct (lo hi : Word) (h : lo ≤ hi) :
    (midFixed lo hi).toNat = (lo.toNat + hi.toNat) / 2 := by
  unfold midFixed; bv_omega

/- If you try the same theorem for `midBuggy`, `bv_decide` fails with:

     The prover found a counterexample, consider the following assignment:
     hi = 4294967295#32
     lo = 4294967295#32

   (0xFFFFFFFF + 0xFFFFFFFF wraps to 0xFFFFFFFE; halved, 0x7FFFFFFF < lo.)
   Any lo = hi ≥ 2^31 works. Turn one into a proof that the buggy version is wrong: -/
theorem midBuggy_wrong : ¬ ∀ lo hi : Word, lo ≤ hi → lo ≤ midBuggy lo hi := by
  intro h
  have := h 0x80000000 0x80000000 (by decide)
  revert this; decide

/-! ## 3. The bounds-check idiom

Every parser has `if (off + len > size) return -1;`. It's wrong: `off + len`
can wrap. The correct form subtracts on the side that can't underflow. -/

def boundsBuggy (off len size : Word) : Bool := off + len ≤ size
def boundsFixed (off len size : Word) : Bool := len ≤ size && off ≤ size - len

/-- The spec is in `Nat`: "the range `[off, off+len)` fits in `[0, size)`". -/
theorem boundsFixed_sound (off len size : Word) (h : boundsFixed off len size = true) :
    off.toNat + len.toNat ≤ size.toNat := by
  simp [boundsFixed] at h; bv_omega

/-- …and it rejects nothing it shouldn't (it's *complete*, not just *sound*). -/
theorem boundsFixed_complete (off len size : Word) (h : off.toNat + len.toNat ≤ size.toNat) :
    boundsFixed off len size = true := by
  simp [boundsFixed]; bv_omega

theorem boundsBuggy_unsound :
    ¬ ∀ off len size : Word, boundsBuggy off len size = true → off.toNat + len.toNat ≤ size.toNat := by
  intro h
  have := h 0xFFFFFFFF 1 0 (by decide)   -- off + len wraps to 0, and 0 ≤ 0 passes
  revert this; decide

/-! ## 4. Counter underflow — the article's decompressor bug, distilled

"A counter underflow in a decompressor causing an out-of-bounds write."
The shape: `remaining -= consumed` where `consumed` came from the input.
If `consumed > remaining`, `remaining` becomes ~4 billion and the next
bounds check passes everything. -/

/-- With the guard, unsigned subtraction means what it says. -/
theorem sub_guarded (remaining consumed : Word) (h : consumed ≤ remaining) :
    (remaining - consumed).toNat = remaining.toNat - consumed.toNat := by
  bv_omega

/-- Without it, "remaining" can *grow*. -/
theorem sub_unguarded : ¬ ∀ remaining consumed : Word, (remaining - consumed) ≤ remaining := by
  intro h
  have := h 0 1
  revert this; decide

/-! ## 5. Bit tricks, settled for all inputs -/

/-- Byte swap (`__builtin_bswap32`) is an involution. -/
def bswap (x : Word) : Word :=
  ((x &&& 0xFF) <<< 24) ||| ((x &&& 0xFF00) <<< 8) ||| ((x >>> 8) &&& 0xFF00) ||| (x >>> 24)

theorem bswap_bswap (x : Word) : bswap (bswap x) = x := by
  unfold bswap; bv_decide

/-- `x & (x-1)` clears the lowest set bit; `x & -x` isolates it. -/
theorem clear_lowest (x : Word) : x &&& (x - 1) = x ^^^ (x &&& (0 - x)) := by
  bv_decide

/-- Branchless min, as seen in crypto code that must not branch on secrets. -/
def minBranchless (a b : Word) : Word :=
  b ^^^ ((a ^^^ b) &&& (0 - (if a < b then 1 else 0)))

theorem minBranchless_correct (a b : Word) :
    minBranchless a b = (if a < b then a else b) := by
  unfold minBranchless; bv_decide

/-- Overflow-free average: `(a & b) + ((a ^ b) >> 1)` equals the exact average,
    computed in 33 bits where nothing can overflow. -/
theorem avg_no_overflow (a b : Word) :
    (a &&& b) + ((a ^^^ b) >>> 1) = ((a.zeroExtend 33 + b.zeroExtend 33) >>> 1).truncate 32 := by
  bv_decide

/-- Signed-overflow detection, the way compilers implement
    `__builtin_add_overflow`: overflow iff the sum's sign differs from both inputs'. -/
theorem sadd_overflow_test (a b : Word) :
    BitVec.saddOverflow a b = (((a + b) ^^^ a) &&& ((a + b) ^^^ b)).msb := by
  bv_decide

/-! ## 6. What did we trust? -/

#print axioms midFixed_correct        -- bv_omega: [propext, Quot.sound] — kernel only
#print axioms minBranchless_correct   -- bv_decide: … plus a `_native.bv_decide` axiom

end Metal.S04
