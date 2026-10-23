import Metal.S08_Trust

/-!
# Exercises — Stage 8: audit the agent

An AI agent was asked to prove the Stage 7 spec for `buggyProg` (the one
with the off-by-one). It came back with four "proofs". Every one of them is
accepted by Lean. Your job is to say why each one doesn't mean what it
claims, and to *prove* your objection where you can. This is the review you
would do before trusting an LLM's proof: you read the statement, never
the proof.

Check: `lake build Exercises.S08_Trust`.
-/

namespace Metal.S08Ex
open Metal Metal.Trust Reg Instr Machine

/-! ## E8.1a ★ The agent's first claim -/
theorem claim_a : ∀ input : List Byte, input.length < maxInput → input.length > maxInput + 5 →
    ExitsCleanly buggyProg (load input) := by
  intro input h1 h2; omega

/-- Prove that no input satisfies the claim's hypotheses. -/
theorem e8_1a : ¬ ∃ input : List Byte, input.length < maxInput ∧ input.length > maxInput + 5 := by
  sorry

/-! ## E8.1b ★ The agent's second claim used `NoFaultWithin` (see the lesson).
Show the weak spec accepts a program that crashes on its very first
instruction, while the real spec rejects it. -/
def crashProg : Program := ⟨[lbu a0 zero 0, li a7 93, ecall]⟩

theorem e8_1b_weak : NoFaultWithin crashProg (load []) := by
  sorry

theorem e8_1b_real : ¬ ExitsCleanly crashProg (load []) := by
  sorry

/-! ## E8.1c ★★ The agent's third claim: it "fixed" the bug.
It changed the length check to `bgeu x0, x0` (always taken). Its proof that
`agentProg` never crashes is perfectly valid. Show that the patch changed the
program's behaviour on a well-formed input: find one where the real fix and
the agent's fix return different exit codes, and prove it.
(`exitCode` is in `S05_Playground.lean`; `decide` or `rfl` will check it.) -/
def agentProg : Program := harness (bgeu zero zero 36)

theorem e8_1c : exitCode fixedProg [0] ≠ exitCode agentProg [0] := by
  sorry   -- replace `[0]` with an input that distinguishes them, then prove it

/-! ## E8.1d ★ The agent's fourth claim. What's wrong? (Answer in a comment;
use `#print axioms`.) Then delete the axiom and see what breaks. -/
axiom agent_lemma : ∀ input : List Byte, ExitsCleanly buggyProg (load input)

theorem claim_d : ∀ input : List Byte, input.length < maxInput → ExitsCleanly buggyProg (load input) :=
  fun input _ => agent_lemma input

-- Your answer:

/-! ## E8.2 ★★★ Close the reward-hacking hole for the capstone
`FixedSpec` only says "no crash", so the agent's do-nothing patch passes it.
Write the *functional* spec: the harness exits with exactly the sum of the
first `n` payload bytes when the record is well-formed, and 0 otherwise.
`capResult` is the reference implementation; check it against the binary
on a few inputs first, then prove the theorem for all inputs.

This is the hardest proof in the course. Model it on `sum_correct` in
`Metal/S08_Trust.lean` (functional invariant) combined with your Stage 7
proof (prologue paths). Two tips that will save you an hour:
* State every fact in the form `simp` will rewrite *to*: `input.tail`, not
  `input.drop 1`; `j + 1`, not `1 + j`. A hypothesis whose left-hand side
  isn't in simp-normal form is silently ignored by `sym`.
* After you've split off the empty case, `generalize hin : b :: rest = input`
  makes the input opaque so `simp` can't rewrite `(b :: rest).length`. -/
def capResult (input : List Byte) : Word :=
  match input with
  | []        => 0
  | n :: rest => if n.toNat < input.length then checksum (rest.take n.toNat) else 0

example : exitCode fixedProg [2, 10, 20] = some 30 := by rfl
example : capResult [2, 10, 20] = 30 := by rfl

theorem e8_2 (input : List Byte) (hlen : input.length < maxInput) :
    ExitsWith fixedProg (load input) (capResult input) := by
  sorry

end Metal.S08Ex
