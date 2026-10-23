import Metal.S05_Machine

/-!
# Stage 6a — A proof library for symbolic execution

`S05_Machine.lean` is the *trusted* model. This file is the opposite: an
*untrusted* toolbox of lemmas and one tactic. Nothing here can make a false
theorem provable — every lemma below is itself checked by Lean's kernel. If a
lemma were wrong, it would simply fail to compile. That asymmetry is the whole
reason an LLM is allowed to write files like this one.

In the article's proofs, the analogous library (theorem-labs'
`theories/Common/` — `SymTac.v`, `SymBranch.v`, `WalkTac.v`, …) is shared
between hundreds of proofs. That reuse is where their "17% fewer tokens with a
shared workspace" comes from.

What is in here:

1. `run_add`   — running a+b steps = running a steps, then b steps.
                 This lets us cut a long execution into pieces (prologue, loop,
                 epilogue) and prove each piece separately.
2. A *simp set*: lemmas saying how `reg`, `pc`, `canRead`, `mem` look after
   `setReg` / `setPc`, and what the initial `load` state contains.
3. `sym` — a tactic that is literally `simp` with the semantics unfolded and
   the simp set above. Each call pushes the symbolic state forward through as
   many instructions as `simp` can resolve. That is symbolic execution.
-/

namespace Metal
open Reg Instr Machine

/-! ## Sequencing executions -/

/-- "Then": if the first part is still running, continue with `f`; a halt or
    a fault is final. (The monadic bind of `Outcome`, for the curious.) -/
def Outcome.bind : Outcome → (Machine → Outcome) → Outcome
  | .running m, f => f m
  | o,          _ => o

@[simp] theorem Outcome.bind_running (m : Machine) (f : Machine → Outcome) :
    (Outcome.running m).bind f = f m := rfl

/-- **Cut lemma.** `a + b` steps = `a` steps, then `b` more.
    Proof: induction on `a` — the first time you see the pattern that every
    loop proof in this repo uses. -/
theorem run_add (p : Program) (a b : Nat) (m : Machine) :
    run p (a + b) m = (run p a m).bind (run p b) := by
  induction a generalizing m with
  | zero => simp [run]
  | succ n ih =>
    rw [Nat.add_right_comm]
    simp only [run]
    cases step p m <;> simp [ih, Outcome.bind]

/-- Convenience form of `run_add` when we already know how the first part ends. -/
theorem run_add_of_running (p : Program) (a b : Nat) (m m' : Machine)
    (h : run p a m = .running m') : run p (a + b) m = run p b m' := by
  rw [run_add, h]; rfl

/-- If the first part halts, the whole run halts the same way. -/
theorem run_add_of_halted (p : Program) (a b : Nat) (m : Machine) (c : Word)
    (h : run p a m = .halted c) : run p (a + b) m = .halted c := by
  rw [run_add, h]; rfl

/-! ## Determinism: crashes and exits are final

A longer run starts the same way as a shorter one. So once a run has
crashed, no bigger budget can make it exit; and a program can't exit with two
different codes. These are what let us turn one concrete crashing run into a
proof that the spec is *false* (Stage 7). -/

theorem run_le (p : Program) (m : Machine) (a b : Nat) (hab : a ≤ b) :
    run p b m = (run p a m).bind (run p (b - a)) := by
  rw [← run_add]; congr 1; omega

theorem fault_final (p : Program) (m : Machine) (k : Nat) (f : Fault)
    (hk : run p k m = .fault f) : ¬ ExitsCleanly p m := by
  intro ⟨n, c, hn⟩
  by_cases h : n ≤ k
  · -- the shorter run already halted, so the longer one halts too: contradiction
    rw [run_le p m n k h, hn] at hk; cases hk
  · -- the longer run must agree with the crash
    rw [run_le p m k n (by omega), hk] at hn; cases hn

/-- Determinism, the other way round: a program can't exit with two different codes. -/
theorem halted_unique (p : Program) (m : Machine) (a b : Nat) (c₁ c₂ : Word)
    (ha : run p a m = .halted c₁) (hb : run p b m = .halted c₂) : c₁ = c₂ := by
  by_cases h : a ≤ b
  · rw [run_le p m a b h, ha] at hb; cases hb; rfl
  · rw [run_le p m b a (by omega), hb] at ha; cases ha; rfl


/-! ## The simp set: how the state changes

Each lemma is one fact a C programmer would take for granted ("writing a
register doesn't move the pc"). We have to *say* them, once, and prove them,
once; afterwards `simp` uses them thousands of times. -/

@[simp] theorem reg_setReg (m : Machine) (r r' : Reg) (v : Word) :
    (m.setReg r v).reg r' = if r' = 0 then 0 else if r' = r then v else m.reg r' := by
  unfold Machine.reg Machine.setReg; by_cases h : r' = 0 <;> simp [h]
@[simp] theorem reg_setPc (m : Machine) (r : Reg) (pc : Word) :
    (m.setPc pc).reg r = m.reg r := rfl
@[simp] theorem reg_setMem (m : Machine) (r : Reg) (a : Word) (b : Byte) :
    (m.setMem a b).reg r = m.reg r := rfl
@[simp] theorem reg_x0 (m : Machine) : m.reg 0 = 0 := rfl

@[simp] theorem pc_setReg (m : Machine) (r : Reg) (v : Word) : (m.setReg r v).pc = m.pc := rfl
@[simp] theorem pc_setPc (m : Machine) (pc : Word) : (m.setPc pc).pc = pc := rfl
@[simp] theorem pc_setMem (m : Machine) (a : Word) (b : Byte) : (m.setMem a b).pc = m.pc := rfl

@[simp] theorem canRead_setReg (m : Machine) (r : Reg) (v : Word) :
    (m.setReg r v).canRead = m.canRead := rfl
@[simp] theorem canRead_setPc (m : Machine) (pc : Word) : (m.setPc pc).canRead = m.canRead := rfl
@[simp] theorem canRead_setMem (m : Machine) (a : Word) (b : Byte) :
    (m.setMem a b).canRead = m.canRead := rfl
@[simp] theorem canWrite_setReg (m : Machine) (r : Reg) (v : Word) :
    (m.setReg r v).canWrite = m.canWrite := rfl
@[simp] theorem canWrite_setPc (m : Machine) (pc : Word) : (m.setPc pc).canWrite = m.canWrite := rfl
@[simp] theorem canWrite_setMem (m : Machine) (a : Word) (b : Byte) :
    (m.setMem a b).canWrite = m.canWrite := rfl

@[simp] theorem mem_setReg (m : Machine) (r : Reg) (v : Word) : (m.setReg r v).mem = m.mem := rfl
@[simp] theorem mem_setPc (m : Machine) (pc : Word) : (m.setPc pc).mem = m.mem := rfl

/-! Branch conditions, unfolded to plain comparisons. -/
@[simp] theorem Cond.eval_eq  (a b : Word) : Cond.eq.eval a b  = (a == b) := rfl
@[simp] theorem Cond.eval_ne  (a b : Word) : Cond.ne.eval a b  = (a != b) := rfl
@[simp] theorem Cond.eval_ltu (a b : Word) : Cond.ltu.eval a b = a.ult b := rfl
@[simp] theorem Cond.eval_geu (a b : Word) : Cond.geu.eval a b = !(a.ult b) := rfl

/-! What the loader sets up. -/
@[simp] theorem load_pc (input : List Byte) : (load input).pc = 0 := rfl
@[simp] theorem load_canRead (input : List Byte) :
    (load input).canRead = inInput input.length := rfl
@[simp] theorem load_canWrite (input : List Byte) : (load input).canWrite = fun _ => false := rfl
@[simp] theorem load_reg (input : List Byte) (r : Reg) :
    (load input).reg r = if r = 0 then 0 else if r = a0 then inputBase
      else if r = a1 then BitVec.ofNat 32 input.length else 0 := rfl

/-! ## The `sym` tactic

`sym` unfolds `run`, `step`, `fetch` and `exec`, looks up the instruction at
the (concrete) pc, and applies the simp set. Extra facts go in brackets, e.g.
`sym [myProg, hpc, ha0]`: you always pass the program, plus whatever
hypotheses tell `simp` the pc, the registers and the bounds checks.

There is no magic here: `sym` is a macro for one `simp` call. When it gets
stuck, the leftover goal shows you exactly which fact it needed: usually a
branch condition or a bounds check. You prove that fact separately (with
`bv_omega`, `omega` or `bv_decide`) and pass it in. -/

syntax "sym" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| sym) => `(tactic| sym [])
  | `(tactic| sym [$xs,*]) =>
    `(tactic| set_option linter.unusedSimpArgs false in
        simp [run, step, Program.fetch, exec, sext,
          Reg.zero, Reg.ra, Reg.sp, Reg.t0, Reg.t1,
          Reg.a0, Reg.a1, Reg.a2, Reg.a3, Reg.a4, Reg.a5, Reg.a7, $xs,*])

/-! ## Facts about addresses in the input buffer

The loop proofs keep needing two facts: "base + i is inside the buffer when
i < len", and "base + i = base + j iff i = j" (no wrap-around). Both hold
because `inputBase + maxInput < 2^32`: the whole buffer fits in the address
space. That premise is *part of the model*: if the loader could put a 64 MiB
buffer at 0xFFFF0000, these lemmas would be false and so would our theorems. -/

theorem inInput_of_lt (len i : Nat) (hlen : len < maxInput) (hi : i < len) :
    inInput len (inputBase + BitVec.ofNat 32 i) = true := by
  simp [inInput, inputBase, maxInput] at *
  bv_omega

theorem inInput_of_ge (len i : Nat) (hlen : len < maxInput) (hi : len ≤ i) (hi' : i < maxInput) :
    inInput len (inputBase + BitVec.ofNat 32 i) = false := by
  simp [inInput, inputBase, maxInput] at *
  bv_omega

theorem addr_eq_iff (i j : Nat) (hi : i < maxInput) (hj : j < maxInput) :
    inputBase + BitVec.ofNat 32 i = inputBase + BitVec.ofNat 32 j ↔ i = j := by
  simp only [inputBase, maxInput] at *
  constructor <;> intro h <;> bv_omega

/-- The same, in the shape `simp` leaves after `p++` (`addi a0, a0, 1`). -/
theorem addr_succ_eq_iff (i j : Nat) (hi : i + 1 < maxInput) (hj : j < maxInput) :
    inputBase + BitVec.ofNat 32 i + 1#32 = inputBase + BitVec.ofNat 32 j ↔ i + 1 = j := by
  simp only [inputBase, maxInput] at *
  constructor <;> intro h <;> bv_omega

/-- `p++` moves the pointer from `base + i` to `base + (i+1)`. -/
theorem addr_succ (i : Nat) :
    inputBase + BitVec.ofNat 32 i + 1#32 = inputBase + BitVec.ofNat 32 (i + 1) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

end Metal
