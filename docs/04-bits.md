# 04 — Bits, bytes, and overflow

*Time: 3–4 hours. Files: `Metal/S04_Bits.lean`, `Exercises/S04_Bits.lean`.*

## Why this stage exists

The article's bugs are your bugs: a counter underflow that turns a length into
4 billion; an index that wraps; a bounds check that overflows. Machine-level
proofs (Stages 5–8) are full of `BitVec 32` arithmetic. This stage gives you
the tools to settle such questions for all 2^32 or 2^64 inputs, and, when the
answer is "it can break", to get the input that breaks it.

## `BitVec n`: `uintN_t` with a precise meaning

| Lean | C | |
|---|---|---|
| `x : BitVec 32` | `uint32_t x` | arithmetic mod 2^32 |
| `5#8` | `(uint8_t)5` | literal with width |
| `x.toNat` | `(unsigned long long)x`, as a mathematical integer | unsigned meaning |
| `x.toInt` | `(int32_t)x` | two's-complement meaning |
| `x < y`, `x ≤ y` | unsigned compare | |
| `x.slt y` | signed compare | |
| `x.signExtend 32` | `(int32_t)(int8_t)x` | |
| `x.zeroExtend 32` / `setWidth` | `(uint32_t)(uint8_t)x` | |
| `x &&& y`, `|||`, `^^^`, `~~~` | `&`, `|`, `^`, `~` | |
| `x <<< n`, `x >>> n` | `<<`, `>>` (logical) | |

The pattern for every spec in this stage: **state the property in `Nat`** (where
nothing overflows) **about values computed in `BitVec`**. If the property
holds, the code doesn't overflow in a way that matters. If not, you get a
counterexample.

## Two decision procedures

* **`bv_omega`**: converts the goal to statements about `.toNat` (making each
  `mod 2^n` explicit) and runs `omega`. Handles `+`, `-`, `<`, `≤`, constants.
  Fully kernel-checked. This is the one the machine proofs use.
* **`bv_decide`**: bit-blasts the goal into a SAT problem, runs the CaDiCaL
  solver, and checks its certificate. Handles everything, including bitwise
  ops, shifts, multiplication and `if`. **Gives a counterexample when the claim
  is false.**

### The trust detail (preview of Stage 8)

`bv_decide` is a small instance of the article's architecture: an untrusted,
fast search engine (the SAT solver) plus a certificate (an LRAT proof) that is
checked. In Lean 4.35 that check runs as *compiled native code* rather than in
the kernel, so `#print axioms` shows an extra axiom:

```
'Metal.S04.midFixed_correct' depends on axioms: [propext, Quot.sound]           -- bv_omega
'Metal.S04.minBranchless_correct' depends on axioms: [propext, Classical.choice,
   Quot.sound, minBranchless_correct._native.bv_decide.ax_1_5]                    -- bv_decide
```

That extra line means "also trust Lean's compiler and runtime." It's a
reasonable trade for bit-twiddling lemmas, and a choice you should make
knowingly. The Stage 9 guard rejects it for the lab.

## Walk-through

1. **Reading BitVec** — run the `#eval`s. Note `0x80000000 < 1` is false but
   `0x80000000.slt 1` is true.
2. **The midpoint bug** — `(lo + hi) / 2` overflows (it was in the JDK's binary
   search for nine years). `midFixed_correct` says the fix computes the
   *mathematical* midpoint, stated in `Nat`. The comment shows `bv_decide`'s
   counterexample for the buggy version (`lo = hi = 0xFFFFFFFF`), and
   `midBuggy_wrong` turns it into a proof.
3. **The bounds-check idiom** — `if (off + len > size)` wraps. The fix,
   `len <= size && off <= size - len`, is proved **sound** (accepts only safe
   ranges) *and* **complete** (rejects nothing safe). Ask for both, always: a
   check that rejects everything is sound.
4. **Counter underflow** — the article's decompressor bug, distilled:
   `remaining - consumed` with `consumed > remaining`.
5. **Bit tricks** — bswap is an involution, `x & (x-1)`, branchless min,
   overflow-free average, the signed-overflow test compilers use for
   `__builtin_add_overflow`. Each one is settled for all inputs in milliseconds.

## Exercises: true or false? (`Exercises/S04_Bits.lean`)

Ten claims about words. **Some are false.** Predict first (write your guess
down!), then ask `bv_decide`. If false, put `¬` in front and prove the
negation from the counterexample. Several are bugs you've seen in production:
signed/unsigned mixing (E4.5), sign-extension of bytes (E4.8), the allocator
round-up that wraps near the top of memory (E4.9).

E4.11 ★★★ fixes E4.9 *with a type*: `alignUp4 : Word → Option Word` returns
`none` exactly when rounding would wrap, and you prove it correct.

## Check yourself

1. Why state the midpoint's correctness in `Nat` rather than `BitVec`?
2. A bounds check is *sound* but not *complete*. Is that a security bug? What
   kind of bug is it?
3. What does `bv_decide`'s extra axiom mean you're trusting? Why might the
   article's authors avoid anything like it in their proofs?
4. `(x + 3) & ~3` appears in your allocator. For which `x` is it wrong, and what
   would a caller see?

Next: **[05 — A machine you can prove things about](05-machine.md)**.
