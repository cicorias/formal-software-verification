import Metal.S07_Capstone

/-!
# Stage 8 — What did we actually prove? (Trust, vacuity, and reward hacking)

The article's caveat: *"formally verified" does not mean "bug-free"*. Lean
guarantees one thing only: **the proof proves the statement**. Whether the
statement means what you think, about the machine you think, is on you.

Your trusted computing base (TCB) for `sum_never_crashes` is:

| Piece                                  | Here                         | In the article                          |
|----------------------------------------|------------------------------|-----------------------------------------|
| The proof checker                      | Lean's kernel                | Rocq's kernel (+ OCaml, OS, hardware)   |
| The machine semantics                  | `S05_Machine.lean` (`exec`)  | RISC-V semantics (theorem-labs)         |
| The OS / process model                 | `load`, the `exit` ecall     | Linux process model                     |
| The binary actually being run          | our hand transcription (!)   | the ELF, snapshotted by a tool          |
| The theorem *statement*                | `ExitsCleanly`, `maxInput`   | "the fuzz target exits 0 or 2"          |

Everything else — `S06_SymExec.lean`, every lemma, every tactic, every line
of every proof — is *untrusted*. It could be written by a careless intern or
a reward-hacking AI; it doesn't matter, because the kernel re-checks it.

This file demonstrates, with code that compiles, each way the trusted part
can betray you. Read `docs/08-trust.md` alongside.
-/

namespace Metal.Trust
open Metal Reg Instr Machine

/-! ## Hole 1: a spec that sounds right and says nothing

"There is a number of steps within which the program hasn't faulted."
Sounds like "doesn't crash". It is true of *every* program: take 0 steps. -/

def NoFaultWithin (p : Program) (m : Machine) : Prop :=
  ∃ fuel, ∀ f, run p fuel m ≠ .fault f

theorem everything_is_safe (p : Program) (m : Machine) : NoFaultWithin p m :=
  ⟨0, fun f h => by simp [run] at h⟩

/-- So, "proved": the buggy harness never crashes. 🙃 -/
theorem buggy_is_safe_lol : ∀ input, NoFaultWithin buggyProg (load input) :=
  fun _ => everything_is_safe _ _

/-! The fix was already in Stage 5: `ExitsCleanly` puts the quantifiers the
other way round *and* demands the program actually reaches `exit`. Quantifier
order is the #1 source of spec bugs. Read every `∀`/`∃` out loud. -/

/-! ## Hole 2: a vacuous precondition

If the hypotheses can never hold, the theorem holds for free. Here someone
"tightened" the size bound and got the inequality backwards. -/

theorem buggy_is_safe_vacuously :
    ∀ input : List Byte, input.length > maxInput → input.length < 1 →
      ExitsCleanly buggyProg (load input) := by
  intro input h1 h2
  exact absurd h1 (by omega)   -- no input satisfies both hypotheses

/-! Defense: prove your hypotheses are *satisfiable*: exhibit an input that
meets them. The theorem-labs model does this with `IMAGE_WF` checks, "so that
the statement is not true only because an image cannot run". -/

/-! ## Hole 3: reward hacking — change the program, not the proof

The article (footnote 6): Claude could "trivially satisfy a spec by rewriting
a program so it never crashes." Here's that patch: a harness that exits
immediately. It satisfies the Stage 6/7 spec perfectly. -/

def patchedProg : Program := ⟨[
  li a0 0,
  li a7 93,
  ecall
]⟩

theorem patched_never_crashes :
    ∀ input : List Byte, input.length < maxInput → ExitsCleanly patchedProg (load input) :=
  fun _ _ => ⟨3, 0, by sym [patchedProg]⟩

/-! Defenses, from the article: penalise patches, make the agent characterise
which inputs a patch changes, log and audit every patch. And — the one a
proof can enforce — **strengthen the spec** so that doing nothing fails it.

For `sum`, "doesn't crash" becomes "exits with the right answer": -/

/-- The reference implementation, in plain Lean: add up the bytes mod 2^32,
    left to right, exactly as the C loop does. -/
def checksum (input : List Byte) : Word :=
  input.foldl (fun s b => s + b.setWidth 32) 0

/-- The patched program fails the stronger spec: on input `[1]` it exits
    with 0, not 1. (A machine-checked counterexample, as in Stage 7.) -/
theorem patched_is_wrong :
    ¬ ∀ input : List Byte, input.length < maxInput →
        ExitsWith patchedProg (load input) (checksum input) := by
  intro h
  obtain ⟨fuel, hfuel⟩ := h [1] (by decide)
  -- `patchedProg` exits with 0 after 3 steps, and a program can't exit twice:
  have h3 : run patchedProg 3 (load [1]) = .halted 0 := rfl
  have := halted_unique _ _ _ _ _ _ h3 hfuel   -- 0 = checksum [1]
  revert this; decide

/-! ### And the real program *does* satisfy the strong spec

Same proof shape as Stage 6. The invariant now also tracks the running sum
(`a2`) and that memory still holds the input. This is the difference between
**safety** ("nothing bad happens") and **functional correctness** ("the right
thing happens"). It costs one more invariant clause per value you care about. -/

theorem load_mem (input : List Byte) (i : Nat) (hlen : input.length < maxInput)
    (hi : i < input.length) :
    (load input).mem (inputBase + BitVec.ofNat 32 i) = input[i] := by
  have hin := inInput_of_lt input.length i hlen hi
  have hoff : (inputBase + BitVec.ofNat 32 i - inputBase).toNat = i := by
    simp only [inputBase, maxInput] at *; bv_omega
  simp only [load, hin, ite_true, hoff]
  simp [List.getElem?_eq_getElem hi]

theorem checksum_take_succ (input : List Byte) (i : Nat) (hi : i < input.length) :
    checksum (input.take (i + 1)) = checksum (input.take i) + input[i].setWidth 32 := by
  simp only [checksum, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

structure SumInv (input : List Byte) (i : Nat) (m : Machine) : Prop where
  ctl : LoopInv input.length i m                 -- everything from Stage 6
  a2  : m.reg a2 = checksum (input.take i)       -- s = sum of the first i bytes
  mem : m.mem = (load input).mem                 -- the input hasn't changed

theorem sum_iter (input : List Byte) (i : Nat) (m : Machine)
    (hlen : input.length < maxInput) (hi : i < input.length) (inv : SumInv input i m) :
    ∃ m', run sumProg 4 m = .running m' ∧
      (if i + 1 = input.length then
         m'.pc = 0x28 ∧ m'.reg ra = 4 ∧ m'.reg a2 = checksum input
       else SumInv input (i + 1) m') := by
  have hread := inInput_of_lt input.length i hlen hi
  have hbne  := addr_succ_eq_iff i input.length (by omega) hlen
  have hbyte := load_mem input i hlen hi
  have hsum  := checksum_take_succ input i hi
  have c := inv.ctl
  by_cases h : i + 1 = input.length
  · have htake : input.take (i + 1) = input := by rw [h]; exact List.take_length
    sym [sumProg, c.pc, c.a0, c.a1, c.ra, c.rd, inv.a2, inv.mem, hread, hbne, hbyte, h]
    rw [← hsum, htake]
  · sym [sumProg, c.pc, c.a0, c.a1, c.ra, c.rd, inv.a2, inv.mem, hread, hbne, hbyte, h]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> sym [c.a1, c.ra, c.rd, inv.mem, addr_succ, hsum]

theorem sum_loop (input : List Byte) (hlen : input.length < maxInput) :
    ∀ k i m, i + k = input.length → 0 < k → SumInv input i m →
      ∃ m', run sumProg (4 * k) m = .running m' ∧
        m'.pc = 0x28 ∧ m'.reg ra = 4 ∧ m'.reg a2 = checksum input := by
  intro k
  induction k with
  | zero => intro i m _ hk; omega
  | succ j ih =>
    intro i m hik _ inv
    obtain ⟨m1, h1, h1'⟩ := sum_iter input i m hlen (by omega) inv
    rw [show 4 * (j + 1) = 4 + 4 * j by omega, run_add_of_running _ _ _ _ _ h1]
    by_cases hj : j = 0
    · subst hj
      simp only [show i + 1 = input.length by omega, ite_true] at h1'
      exact ⟨m1, rfl, h1'⟩
    · simp only [show i + 1 ≠ input.length by omega, ite_false] at h1'
      exact ih (i + 1) m1 (by omega) (by omega) h1'

/-- **Functional correctness**: the binary exits with exactly the checksum of
    its input, for every input under 64 MiB. The patched program can't pass
    this; only a program that really sums the bytes can. -/
theorem sum_correct (input : List Byte) (hlen : input.length < maxInput) :
    ExitsWith sumProg (load input) (checksum input) := by
  by_cases h0 : input.length = 0
  · have hnil : input = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    exact ⟨7, rfl⟩
  · have hne : BitVec.ofNat 32 input.length ≠ 0#32 := by
      simp only [maxInput] at hlen; bv_omega
    have : ∃ m, run sumProg 4 (load input) = .running m ∧ SumInv input 0 m := by
      sym [sumProg, hne]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> sym [checksum]
    obtain ⟨m, hrun, inv⟩ := this
    obtain ⟨m', hloop, hpc, hra, ha2⟩ :=
      sum_loop input hlen input.length 0 m (by omega) (by omega) inv
    refine ⟨4 + (4 * input.length + 4), ?_⟩
    rw [run_add_of_running _ _ _ _ _ hrun, run_add_of_running _ _ _ _ _ hloop]
    sym [sumProg, hpc, hra, ha2]

/-! ## Hole 4: the model is wrong

Suppose the process model forgot to install the ASan shadow map, i.e. every
address is readable. (Real-world analogue: proving facts about a build
without sanitizers, or a semantics where out-of-bounds loads return 0.)
The Stage 7 counterexample *vanishes*: -/

def loadNoAsan (input : List Byte) : Machine :=
  { load input with canRead := fun _ => true }

theorem buggy_fine_without_asan : ExitsCleanly buggyProg (loadNoAsan [1]) :=
  ⟨20, 0, by rfl⟩   -- reads data[1] (unmapped, reads as 0) and exits happily

/-! Nothing in Lean can catch this. The model is an *assumption*. The real
model (theorem-labs/rocq-linux-process-semantics) spends a whole document,
`SCOPE.md`, listing where it is narrower than reality: one thread, no signal
handlers, static binaries only, an 8 MiB stack, … A proof says nothing about
a program outside that scope. -/

/-! ## Hole 5: extra axioms

An `axiom` is a claim with no proof. One false axiom proves everything.
`sorry` is an axiom (`sorryAx`). `native_decide` trusts the compiler and
introduces an axiom too. `#print axioms` is your audit. -/

/-- A "proof" that would pass a careless review. -/
axiom trust_me_its_fine : FixedSpec

theorem fixed_never_crashes_trust_me : FixedSpec := trust_me_its_fine

/-- info: 'Metal.Trust.fixed_never_crashes_trust_me' depends on axioms: [propext, Quot.sound, trust_me_its_fine] -/
#guard_msgs in #print axioms fixed_never_crashes_trust_me

/-- `native_decide` compiles the check to C and runs it; the kernel
    doesn't re-check, so Lean records an axiom that says "trust the compiler". -/
theorem big_sum_native : (List.range 2000).foldl (· + ·) 0 = 1999000 := by native_decide

/-- The same fact, checked by the kernel itself. Slower, but nothing extra to trust. -/
theorem big_sum_kernel : (List.range 2000).foldl (· + ·) 0 = 1999000 := by decide +kernel

#print axioms big_sum_native   -- [big_sum_native._native.native_decide.ax_1_1]
#print axioms big_sum_kernel   -- (no axioms)

/-! ## Hole 6: the binary isn't the binary

We typed `sumProg` in by hand from clang's `.s` output. Did we transcribe it
correctly? Is the `.s` what the linker put in the ELF? Our proofs can't say.
The article's pipeline closes this by snapshotting the actual ELF bytes
(`tools/elf_snapshot.py` in theorem-labs) and *decoding* them with a decoder
that is itself part of the trusted model. The statement then names the binary
by its SHA-256. "We proved something about a binary other than the one we
ship" is a real failure mode; pin the artefact.

## The audit checklist (use it on every proof, yours or an AI's)

1. Read the **statement**, not the proof. Every quantifier, out loud.
2. Are the hypotheses satisfiable? Exhibit a witness.
3. Is the program the one you ship? (hash) Was it patched? (diff)
4. Is the spec strong enough that "do nothing" fails it? (try it!)
5. `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
6. What does the model leave out? (threads, signals, the OS, the hardware…)
-/

end Metal.Trust
