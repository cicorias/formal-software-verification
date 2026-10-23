# 07 — Capstone: a fuzz harness, a bug, a fix, a proof

*Time: 6–10 hours. Files: `c/harness_buggy.c`, `c/harness_fixed.c`,
`Metal/S07_Capstone.lean`, `Exercises/S07_Capstone.lean`.*

The article's loop, end to end, on one function you can hold in your head:
harness → binary → spec → failed proof → bug → patch → proof.

## The harness

```c
// Record format: [n][payload: n bytes]. Sum the payload.
uint32_t LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  if (size == 0) return 0;
  size_t n = data[0];
  if (n > size) return 0;           // BUG: payload starts at data[1], so need n <= size-1
  uint32_t s = 0;
  for (size_t i = 0; i < n; i++) s += data[1 + i];
  return s;
}
```

On input `[1]` (n = 1, size = 1) the check passes and the loop reads
`data[1]`, one byte past the end.

```sh
make -C c demo
== The off-by-one harness: random inputs find it almost immediately
==ERROR: AddressSanitizer: heap-buffer-overflow ... READ of size 1
```

Yes, a fuzzer finds *this* bug instantly; it's here to teach the mechanics,
not to beat fuzzers (Stage 3 did that). What a fuzzer can't do is tell you the
fix is right for *every* input.

## The binary

`make -C c asm`, then diff the two harnesses' assembly:

```
<   bltu  a1, a3, .LBB0_5        ; buggy:  if (size <u n) reject
>   bgeu  a3, a1, .LBB0_5        ; fixed:  if (n >=u size) reject
```

**The bug is one instruction.** `Metal/S07_Capstone.lean` defines the harness
once, `harness (reject : Instr)`, and instantiates it twice.

## Step 1: run it

The `#eval`s: `[]` → 0, `[2,10,20]` → 30, `[5,10,20]` → 0 (rejected),
`[1]` → `CRASH: Metal.Fault.badRead 0x00010001#32` (address 0x10001) on the buggy one and `exit(0)` on the fixed
one. Use `trace buggyProg [1]` to watch it happen.

## Step 2: try to prove the buggy one, and get stuck

The same proof structure as Stage 6, with one new twist: the loop bound `n`
comes *from the input* (it's `data[0]`). So the loop invariant has to carry
"`1 + n ≤ size`", a fact established by the length check before the loop.

With `bltu a1, a3` (reject if `size < n`), what you learn on the fall-through
path is `n ≤ size`, not `n + 1 ≤ size`. The one-iteration lemma's
precondition `i < e ≤ len` (needed for `inInput_of_lt`) can't be established
for the last iteration. **The stuck goal is the bug report:** it says
"I need `1 + n ≤ size` and I only have `n ≤ size`", which is a precise
description of the off-by-one.

## Step 3: turn the counterexample into a theorem

```lean
theorem buggy_crashes : run buggyProg 12 (load [1]) = .fault (.badRead 0x10001) := by rfl

theorem buggy_violates_spec :
    ¬ ∀ input, input.length < maxInput → ExitsCleanly buggyProg (load input)
```

The second needs `fault_final`: a crash after 12 steps means no step budget
reaches `exit`, because `run` is deterministic (a longer run starts the same
way). This is what "Claude found a bug" looks like as an artefact: not a log
line, a theorem.

## Step 4: fix and prove (your job)

`Exercises/S07_Capstone.lean` has the roadmap:

1. `loop_iter` — one trip around the loop at 0x30.
2. `loop_all` — induction on iterations left.
3. `exit_from_0x40` — `ret`, `li`, `ecall`.
4. `n_facts` — three facts about `n` as a 32-bit value (`zext(n) <u size` iff
   `n < size`; `zext(n) == 0` iff `n = 0`; `data + 1 + zext(n) = data + (1+n)`).
5. `fixed_never_crashes` — four paths through the prologue:

| Path | Condition | Steps to `exit` |
|---|---|---|
| empty | `size = 0` | 6 |
| rejected | `n ≥ size` (the fixed check) | 9 |
| nothing to sum | `n = 0` | 10 |
| the loop | `1 ≤ n < size` | 10 + 4n + 3 |

Hints that will save you time:

* Don't learn the value of `n`. Keep it as the symbolic byte
  `(load input).mem inputBase` and case-split on its `toNat`.
* On some paths `simp` rewrites the `size == 0` test into `input = []` (via
  `List.length_eq_zero`) before it can use your `ofNat … ≠ 0` fact. If a goal
  still contains `if input = [] then …`, pass `hnil : input ≠ []` to `sym`.
* If `sym` leaves `0#32 = ?m`, supply the exit code explicitly.
* Count steps with `trace fixedProg [2, 10, 20]`.

## Reflection (write the answer in the exercise file)

Where *exactly* does your proof break if you point it at `buggyProg`? Which
hypothesis can't you establish, at which instruction? Compare with the article:
*"the process of attempting to prove these specs discovered hundreds of bugs."*
Now you know what that process looks like from the inside.

## What the article did next, and you will in Stage 8

Our `FixedSpec` says "no crash." A "fix" that makes the harness reject every
input (`bgeu zero, zero, …`) also satisfies it. The article's authors knew:
they *"penalized any patch and offered extra credit for proving which inputs it
changes and how few they are."* Stage 8 closes the hole with a functional spec.

Next: **[08 — Trust](08-trust.md)**.
