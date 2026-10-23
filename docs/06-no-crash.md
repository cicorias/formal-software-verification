# 06 — Proving a compiled loop never crashes, for every input

*Time: 6–8 hours. Files: `Metal/S06_SymExec.lean` (the proof library),
`Metal/S06_NoCrash.lean` (the proof), `Exercises/S06_NoCrash.lean`.*

This is the core of the course: the article's method, on a 12-instruction
binary instead of an 18,000-instruction one.

## The program

```c
uint32_t sum(const uint8_t *p, uint32_t len) {
  uint32_t s = 0;
  for (uint32_t i = 0; i < len; i++) s += p[i];
  return s;
}
```

clang -O1 for RV32I, behind a `_start` that calls `sum(data, size)` and exits:

```
0x00 _start: jal  ra, sum          0x18 .loop: lbu  a3, 0(a0)     ← the only load
0x04         li   a7, 93           0x1c        addi a0, a0, 1
0x08         ecall                 0x20        add  a2, a2, a3
0x0c sum:    li   a2, 0            0x24        bne  a0, a1, .loop
0x10         beqz a1, .done        0x28 .done: mv   a0, a2
0x14         add  a1, a0, a1       0x2c        ret
```

Notice clang turned `i < len` into "pointer != end pointer". A proof about
the C source wouldn't see that; ours is about what the CPU runs.

**The theorem**:

```lean
theorem sum_never_crashes :
    ∀ input : List Byte, input.length < maxInput → ExitsCleanly sumProg (load input)
```

For every input under 64 MiB, the binary reaches `exit` without faulting.

## The shape of the proof (Hoare logic, informally)

Think in **Hoare triples**: `{P} code {Q}` means "if `P` holds before `code`
runs, `Q` holds after." The proof cuts the execution into three pieces:

```
 load input ──prologue──▶ {LoopInv 0} ──loop body ×len──▶ {at .done} ──epilogue──▶ exit
   (4 steps)                (4 steps per iteration)                 (4 steps)
```

1. **Prologue**: from the initial state, 4 instructions reach `.loop` with the
   invariant holding for `i = 0` (or, for the empty input, 3 reach `.done`).
2. **Loop invariant** at pc = 0x18 after `i` iterations:
   * `a0 = data + i` (the pointer)
   * `a1 = data + len` (the end pointer)
   * `ra = 4` (the return address survives)
   * the shadow map is unchanged
3. **One iteration**: if the invariant holds at `i` and `i < len`, then 4
   instructions later either it holds at `i+1`, or (if `i+1 = len`) we're at
   `.done` with `ra = 4`. *The `lbu` is safe because `data + i` is in the buffer
   when `i < len`*. That one fact is the whole safety argument.
4. **All iterations**: induction on `k = len − i`, the iterations remaining.
   `k` is the **variant**: it decreases every time round, which is why the loop
   terminates. Invariant ⇒ safe; variant ⇒ ends.
5. **Epilogue**: `mv`, `ret`, `li a7 93`, `ecall` → `.halted`.
6. **Glue**: `run_add` says running `a + b` steps is running `a`, then `b`. So
   `4 + 4·len + 4` steps from `load input` reach `exit`.

That's the article's proof structure exactly. Their invariants have more
fields (heap metadata, ASan shadow state, libc's internal state) and there are
many more of them, but each is this.

## Symbolic execution with `sym`

How do we "run 4 instructions" when we don't know the input? With
**symbolic execution**: `simp` unfolds `run`/`step`/`exec`, looks up the
instruction at the (known) pc, and rewrites the state with a simp set of
lemmas like:

```lean
@[simp] theorem reg_setReg : (m.setReg r v).reg r' = if r' = 0 then 0 else if r' = r then v else m.reg r'
@[simp] theorem pc_setPc   : (m.setPc pc).pc = pc
```

The `sym` tactic (`S06_SymExec.lean`) is literally one `simp` call with those
lemmas and the register names. You pass it the facts it needs:

```lean
sym [sumProg, inv.pc, inv.a0, inv.a1, inv.ra, inv.rd, hread, hbne, h]
--   program  where we are, what the registers hold   bounds fact  branch fact
```

When `sym` gets stuck, the leftover goal names the fact it needed: usually
a bounds check (`inInput len (base + i) = true`) or a branch condition
(`base + i + 1 = base + len`). You prove that separately, typically with
`bv_omega`, and pass it in. The library has the common ones:

| Lemma | Says |
|---|---|
| `inInput_of_lt` | `i < len → data + i` is readable |
| `addr_succ_eq_iff` | `data + i + 1 = data + j ↔ i + 1 = j` (no wrap-around) |
| `addr_succ` | `data + i + 1 = data + (i+1)` |
| `run_add`, `run_add_of_running` | cut a run into pieces |
| `fault_final`, `halted_unique`, `run_le` | determinism: crashes and exits are final |

The "no wrap-around" facts hold because `inputBase + maxInput < 2^32`: the
buffer fits in the address space. **That's a modelling assumption**: if the
loader could put a 64 MiB buffer at 0xFFFF0000, those lemmas would be false.

### Trusted vs. untrusted, again

`S05_Machine.lean` is trusted. `S06_SymExec.lean` is **not**: every lemma in it
is checked by the kernel, so a wrong lemma just fails to compile. This is why
the article's shared proof library (`theories/Common/` in theorem-labs) can
be written and extended by AI: the article's "17% fewer tokens with a shared
workspace" is agents reusing exactly this kind of file.

## Walk-through

Read `Metal/S06_NoCrash.lean` top to bottom with the infoview open:

* **Step 0** — `#eval` and a `rfl` test. Always run the program first.
* **Step 1** — `LoopInv`, a `structure` of facts: write invariants as structs,
  one field per fact; you'll refer to them as `inv.a0`, `inv.pc`, ….
* **Step 2** — `loop_iter`. Two cases on `i + 1 = len`. In each, put the cursor
  after `sym […]` and look at what's left. In the "continue" case, the
  invariant at `i+1` is proved field by field (`constructor <;> sym […]`).
* **Step 3** — `loop_all`: induction on iterations remaining, exactly like
  `sumAcc_eq` in Stage 2, `generalizing` the iteration index and the machine.
* **Steps 4–5** — epilogue, then the theorem, glued with `run_add_of_running`.
* The last line: `#guard_msgs in #print axioms sum_never_crashes`, which *fails
  the build* unless the proof uses only `propext`, `Classical.choice`,
  `Quot.sound`.

## When the kernel is slow

You will hit this one, so here it is up front. Sometimes the editor accepts a
proof in under a second, but `lake build` sits at 100% CPU for minutes and then
dies. That's not `simp`; it's Lean's **kernel** re-checking the proof `simp`
produced. When the proof relies on a definitional unfolding of the initial
state (`load input`) mixed with large constants (like `-1` sign-extended to
`4294967295`), the kernel can end up evaluating `x + 4294967295` by unary
recursion: four billion steps.

**The fix is the same thing that makes proofs readable: checkpoint.** Instead
of symbolically executing six instructions straight from `load input`, prove
an intermediate lemma

```lean
have : ∃ m, run p 2 (load input) = .running m ∧ m.pc = 0x10 ∧ m.reg a0 = … := by sym [p]
obtain ⟨m, hrun, hpc, ha0, …⟩ := this
```

and continue from the abstract `m`, whose registers are hypotheses rather than
things to recompute. `Solutions/S06_NoCrash.lean` (E6.1) shows it. Long,
monolithic symbolic runs are the thing to avoid in general; the article's
600k-line proofs are made of many such checkpoints.

## Exercises (`Exercises/S06_NoCrash.lean`)

| # | What |
|---|---|
| E6.1 ★★ | `last_byte` is safe on every **non-empty** input (straight-line, a negative offset, a checkpoint) |
| E6.2 ★ | …and violates the spec (the empty input; `fault_final`) |
| E6.3 ★★ | `count_zeros` never crashes (the invariant is given; a 5-instruction body) |
| E6.4 ★★★ | `max_byte` never crashes: **write your own invariant**; the loop body takes 4 *or* 6 steps depending on the data |

## Check yourself

1. What is the invariant *for*? What is the variant for? Which one would you
   drop if you only wanted "never faults, but may hang"?
2. Why doesn't the invariant mention `a2` (the running sum)? What theorem would
   need it? (Stage 8.)
3. `addr_succ_eq_iff` needs `j < maxInput`. What breaks if the buffer could end
   at 0xFFFFFFFF?
4. Why is it fine for `S06_SymExec.lean` to be written by an LLM, but not
   `S05_Machine.lean`?

Next: **[07 — Capstone](07-capstone.md)**.
