# 03 — Specifications: saying what "correct" means

*Time: 4–5 hours. Files: `Metal/S03_Specs.lean`, `Exercises/S03_Specs.lean`, `c/rle.c`.*

## Why this stage exists

A proof shows code meets a spec. Nothing checks whether the spec says what you
meant. In the article, every theorem is "this fuzz harness exits normally,"
and the harness's `abort()`-on-failure checks are what make that strong. So
this stage is about the *shapes* properties take, how to test them, how to
prove them, and how they quietly fail to mean anything.

## The running example: RLE

Run-length encoding is the simplest compressor, and mirrors the article's LZO
example ("compress then decompress returns the original"):

```
[7, 7, 7, 9]  ⇄  [3, 7,  1, 9]      -- pairs of [count, value]
```

The count is a byte, so a run longer than 255 must be split. The buggy encoder
forgets that: on 256 equal bytes the count wraps to 0 and 256 bytes vanish.
It's the classic `uint8_t count` overflow.

## Part 1 — Fuzzers sample; the bug lives where they don't go

In the lesson file, the `fuzz` function is a 10-line property tester:
random byte lists, check `decode (encode x) = x`. Run the two `#eval`s:

```
roundtrip (buggy): passed 2000 random tests
roundtrip (fixed): passed 2000 random tests
```

even with a 4-symbol alphabet chosen to make long runs *likely*. The C version
says the same, at scale:

```sh
make -C c demo
== The RLE codec with the 256-run bug: random inputs never find it
200000 inputs (max_len=600, alphabet=4): no crash
== ...but one hand-picked input does (256 x 0x07)
PROPERTY FAILED: round trip
```

The probability of 256 equal bytes in a row from a 4-letter alphabet is about
4^-255. This is the article's 20-MB-with-one-rare-layout bug in miniature:
real, simple, and statistically invisible to random sampling. (A
coverage-guided fuzzer like libFuzzer is much smarter than this one — among
other things it has mutators that insert runs of repeated bytes — so it may
well find this particular bug; try `make -C c libfuzzer` if you have the
runtime. The general point stands: fuzzing gives no guarantee, and the
article's bugs survived years of real, coverage-guided fuzzing.)

`buggy_counterexample` in the lesson then disproves the buggy version with
one concrete input, checked by computation (`decide +kernel`).

## Part 2 — Prove it

The statement we want, `decode (encode xs) = xs`, can't be proved by direct
induction, for the same reason as `sumAcc` in Stage 2: the encoder has state
(the current run). So we prove the **encoder's loop invariant**:

```lean
theorem decode_encodeRun (cur : Byte) (cnt : Nat) (xs : List Byte)
    (h1 : 1 ≤ cnt) (h2 : cnt ≤ 255) :
    decode (encodeRun cur cnt xs) = List.replicate cnt cur ++ xs
```

"If we're in a run of `cnt` copies of `cur`, decoding everything the encoder
emits from here gives back those copies, then the rest of the input." Then
the top-level theorem is one line.

Now look at `toNat_ofNat_byte`: it needs `cnt ≤ 255`. **That hypothesis is
exactly where the buggy encoder's proof gets stuck.** Without the `cnt < 255`
check in the `if`, you can't keep `cnt ≤ 255` as an invariant, and the proof
obligation `(BitVec.ofNat 8 cnt).toNat = cnt` is false at 256. The stuck goal
*is* the bug report. That's what "Claude found bugs while writing the proofs"
means mechanically.

## Part 3 — A spec only says what it says

`encodeLazy` turns every byte `b` into `[1, b]`. It satisfies the round-trip
spec (`lazy_roundtrip`), and never compresses anything. Round-trip is
*necessary* for a codec; it isn't *sufficient*. If compression matters, say so
(`encode_run_small`: a run of k ≤ 255 equal bytes encodes to 2 bytes).

This is the reward-hacking problem from the article in its purest form: an
optimiser (human, compiler, or LLM) given only "make round-trip pass" may
find the cheapest way to pass it. Stage 8 does this to a real binary.

## The catalogue of property shapes

| Shape | Statement | Catches | Fuzz-target form |
|---|---|---|---|
| Round-trip | `decode (encode x) = x` | lossy codecs, wrapping counters | `if (memcmp(dec, in, n)) abort();` |
| Idempotence | `norm (norm x) = norm x` | half-done normalisation | compare two passes |
| Differential | `fast x = reference x` | optimisation bugs | run both, compare |
| Invariant | `valid s → valid (op s)` | data-structure corruption | check after every op |
| Safety | never faults / `isSome` | crashes, OOB, the article's spec | ASan does it for you |
| Bound | `(encode x).length ≤ 2 * x.length` | blow-ups, DoS | `if (out_len > 2*n) abort();` |
| Totality | Lean functions terminate by construction | hangs | a timeout |

## Rules from the people doing this for real

Theorem's OSS Verify instructions for writing fuzz targets that will become
theorems
([`add-project` skill](https://github.com/theorem-labs/oss-verify/blob/main/.claude/skills/add-project/SKILL.md),
[`what-gets-proven.md`](https://github.com/theorem-labs/oss-verify/blob/main/docs/what-gets-proven.md)),
condensed:

1. **Write each property as `if (!cond) abort();`, never `assert()`.** Release
   builds define `NDEBUG`, which deletes every `assert`, and the property
   silently disappears from the theorem. (Our `c/rle.c` follows this.)
2. **Every expected outcome must `return 0`.** Their theorem accepts exit
   statuses 0 and 2 only. Returning `-1` for "property failed" counts as a
   *pass*; returning 1 for "uninteresting input" makes the theorem false.
3. **Show each property can fail.** Make a one-line mutation that breaks it,
   and confirm some input makes the target abort. "A property that no change
   can make fail checks nothing."
4. **Show each check runs.** A coverage witness: inputs that reach every API
   call and every property check at least once.
5. **"A proof is only as strong as its fuzz target. A weak fuzz target makes
   the theorems vacuous."**

Rule 3 is mutation testing for specs, and exercise E3.4 makes you do it: a
mutant encoder that cuts runs at 254 is still a correct codec. Round-trip can't
see the mutation; the compression spec can.

## Exercises (`Exercises/S03_Specs.lean`)

| # | What |
|---|---|
| E3.1 ★★ | Prove the output-size bound (generalise to `encodeRun` first) |
| E3.2 ★ | Show the buggy encoder violates round-trip |
| E3.3 ★★ | **Write** a spec `encodeLazy` fails; prove the real encoder meets it |
| E3.4 ★★ | Mutation analysis: which property notices which change? |
| E3.5 ★★★ | Idempotence of adjacent-dedup (three small inductions) |

## Check yourself

1. Why did 200,000 random tests miss the RLE bug, and why did the proof find it
   in one step?
2. Give a codec that satisfies round-trip *and* the size bound, but is still
   useless. What spec would rule it out?
3. A fuzz harness checks a property with `assert(x == y)`. The project's CI
   builds with CMake `Release`. What does the "never crashes" theorem now say
   about that property?
4. Which property shape would catch a `memcpy`-based "fast path" that differs
   from the slow path on unaligned input?

Next: **[04 — Bits, bytes, and overflow](04-bits.md)**.
