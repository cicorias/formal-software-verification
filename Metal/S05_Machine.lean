/-!
# Stage 5 — A machine you can prove things about

This file is the *semantics*: a precise, executable description of what a tiny
RISC-V CPU does, one instruction at a time. Everything in Stages 6–8 is a
theorem *about* this file. If this file is wrong, those theorems are about the
wrong machine. That is the "trusted model" the article talks about.

We call it **RV-lite**: a subset of RV32I (32-bit RISC-V integer ISA), plus a
one-syscall "Linux" (`exit`), plus an AddressSanitizer-style memory map that
says exactly which bytes a program may touch.

Read `docs/05-machine.md` alongside this file.

Design choices, and what they cost us (all deliberate, all revisited in Stage 8):

* Instructions are an `inductive` (an AST), not 32-bit encodings. The real
  model (theorem-labs/rocq-linux-process-semantics) has a *decoder* from bytes
  to AST too, which is one more thing you have to trust. Code lives in its own
  address space; it is not stored in `mem`, so self-modifying code is impossible.
* Immediates keep their *encoded width* (12, 13, 20, 21 bits) and are
  sign-extended in the semantics, exactly like the real ISA. That is where
  real sign-extension bugs live, so we keep it.
* Memory is a total function `Word → Byte` plus a *shadow map* `canRead` /
  `canWrite`. Touching a byte whose shadow bit is off is a **fault**: that is
  our AddressSanitizer. The real ASan has redzones around each allocation;
  we have "only the input buffer is readable".
* One hart, no interrupts, no CSRs, no misaligned-access subtleties
  (we only have byte loads/stores and word loads/stores with no alignment checks).
* The only syscall is `exit` (a7 = 93, the real Linux RISC-V number).
  Any other `ecall` is a fault: "the model does not cover this". The real model
  calls that `unmodeled`.
-/

namespace Metal

/-- A 32-bit machine word. `BitVec 32` is arithmetic mod 2^32: exactly `uint32_t`. -/
abbrev Word := BitVec 32
/-- A byte. -/
abbrev Byte := BitVec 8
/-- A register number, x0..x31. `Fin 32` = "a natural number below 32". -/
abbrev Reg := Fin 32

/-! ## ABI register names (same as `riscv64-*-objdump` prints them) -/
namespace Reg
abbrev zero : Reg := 0
abbrev ra   : Reg := 1    -- return address
abbrev sp   : Reg := 2    -- stack pointer
abbrev t0   : Reg := 5
abbrev t1   : Reg := 6
abbrev a0   : Reg := 10   -- arg 0 / return value
abbrev a1   : Reg := 11
abbrev a2   : Reg := 12
abbrev a3   : Reg := 13
abbrev a4   : Reg := 14
abbrev a5   : Reg := 15
abbrev a7   : Reg := 17   -- syscall number
end Reg

open Reg

/-! ## Instructions -/

/-- Branch conditions. `ltu`/`geu` compare as unsigned, `lt`/`ge` as signed:
    the same bits, two different orders. Mixing them up is a classic C bug. -/
inductive Cond where
  | eq | ne | lt | ge | ltu | geu
  deriving Repr, DecidableEq

/-- Evaluate a branch condition. `BitVec.slt` is signed `<`, `BitVec.ult` unsigned. -/
def Cond.eval : Cond → Word → Word → Bool
  | .eq,  a, b => a == b
  | .ne,  a, b => a != b
  | .lt,  a, b => a.slt b
  | .ge,  a, b => !(a.slt b)
  | .ltu, a, b => a.ult b
  | .geu, a, b => !(a.ult b)

/-- The RV-lite instruction set. Operand order matches assembly syntax:
    `addi rd, rs1, imm` is `.addi rd rs1 imm`. -/
inductive Instr where
  | lui    (rd : Reg) (imm : BitVec 20)                -- rd := imm << 12
  | addi   (rd rs1 : Reg) (imm : BitVec 12)            -- rd := rs1 + sext(imm)
  | andi   (rd rs1 : Reg) (imm : BitVec 12)            -- rd := rs1 & sext(imm)
  | sltiu  (rd rs1 : Reg) (imm : BitVec 12)            -- rd := (rs1 <u sext(imm)) ? 1 : 0
  | slli   (rd rs1 : Reg) (sh : BitVec 5)              -- rd := rs1 << sh
  | srli   (rd rs1 : Reg) (sh : BitVec 5)              -- rd := rs1 >>u sh
  | add    (rd rs1 rs2 : Reg)                          -- rd := rs1 + rs2
  | sub    (rd rs1 rs2 : Reg)                          -- rd := rs1 - rs2
  | and    (rd rs1 rs2 : Reg)
  | or     (rd rs1 rs2 : Reg)
  | xor    (rd rs1 rs2 : Reg)
  | sltu   (rd rs1 rs2 : Reg)                          -- rd := (rs1 <u rs2) ? 1 : 0
  | lbu    (rd rs1 : Reg) (off : BitVec 12)            -- rd := zext(mem[rs1 + sext(off)])
  | sb     (rs2 rs1 : Reg) (off : BitVec 12)           -- mem[rs1 + sext(off)] := rs2[7:0]
  | branch (c : Cond) (rs1 rs2 : Reg) (off : BitVec 13) -- if c(rs1,rs2) then pc += sext(off)
  | jal    (rd : Reg) (off : BitVec 21)                -- rd := pc+4; pc += sext(off)
  | jalr   (rd rs1 : Reg) (off : BitVec 12)            -- rd := pc+4; pc := (rs1+sext(off)) & ~1
  | ecall                                              -- system call, number in a7
  deriving Repr

/-! Assembler pseudo-instructions, so programs read like `objdump` output. -/
namespace Instr
/-- `li rd, imm` for small immediates (fits in 12 bits). -/
abbrev li (rd : Reg) (imm : BitVec 12) : Instr := .addi rd zero imm
/-- `mv rd, rs` -/
abbrev mv (rd rs : Reg) : Instr := .addi rd rs 0
/-- `ret` = `jalr x0, ra, 0` -/
abbrev ret : Instr := .jalr zero ra 0
abbrev beq  (a b : Reg) (off : BitVec 13) : Instr := .branch .eq a b off
abbrev bne  (a b : Reg) (off : BitVec 13) : Instr := .branch .ne a b off
abbrev bltu (a b : Reg) (off : BitVec 13) : Instr := .branch .ltu a b off
abbrev bgeu (a b : Reg) (off : BitVec 13) : Instr := .branch .geu a b off
/-- `beqz rs, off` = `beq rs, x0, off` -/
abbrev beqz (a : Reg) (off : BitVec 13) : Instr := .branch .eq a zero off
/-- `bnez rs, off` = `bne rs, x0, off` -/
abbrev bnez (a : Reg) (off : BitVec 13) : Instr := .branch .ne a zero off
/-- `seqz rd, rs` = `sltiu rd, rs, 1`  (rd := rs == 0) -/
abbrev seqz (rd rs : Reg) : Instr := .sltiu rd rs 1
/-- `j off` = `jal x0, off` (jump, don't link) -/
abbrev j (off : BitVec 21) : Instr := .jal zero off
end Instr

/-! ## Machine state -/

/-- Everything the CPU and the (tiny) OS know.
    Compare with a C struct: this *is* one, and `{ m with pc := x }` is
    "copy the struct, change one field". Nothing is mutated, ever. -/
structure Machine where
  regs     : Reg → Word      -- register file (x0 is handled by `reg`, below)
  pc       : Word            -- program counter (a byte address)
  mem      : Word → Byte     -- all 4 GiB of byte-addressed memory
  canRead  : Word → Bool     -- shadow map: may this byte be loaded?
  canWrite : Word → Bool     -- shadow map: may this byte be stored?

/-- Why execution stopped abnormally. Each one is a "crash" for our purposes. -/
inductive Fault where
  | badFetch   (pc : Word)    -- jumped to an address with no instruction (SIGSEGV)
  | badRead    (addr : Word)  -- ASan: heap-buffer-overflow READ
  | badWrite   (addr : Word)  -- ASan: heap-buffer-overflow WRITE
  | badSyscall (num : Word)   -- a syscall this model does not cover ("unmodeled")
  deriving Repr, DecidableEq

/-- Result of one step (or of many). Like a C function returning a tagged union. -/
inductive Outcome where
  | running (m : Machine)  -- still going; here is the new state
  | halted  (code : Word)  -- called exit(code)
  | fault   (f : Fault)    -- crashed

namespace Machine

/-- Read a register. x0 always reads as zero, whatever was "written" to it. -/
def reg (m : Machine) (r : Reg) : Word :=
  if r = 0 then 0 else m.regs r

/-- Write a register. Writes to x0 are stored but never observable (see `reg`). -/
def setReg (m : Machine) (r : Reg) (v : Word) : Machine :=
  { m with regs := fun r' => if r' = r then v else m.regs r' }

def setPc (m : Machine) (pc : Word) : Machine := { m with pc := pc }

def setMem (m : Machine) (a : Word) (b : Byte) : Machine :=
  { m with mem := fun a' => if a' = a then b else m.mem a' }

end Machine

/-- A program: a list of instructions, the first at address 0, each 4 bytes. -/
structure Program where
  code : List Instr

/-- Instruction fetch. A misaligned or out-of-range pc fetches nothing. -/
def Program.fetch (p : Program) (pc : Word) : Option Instr :=
  if pc.toNat % 4 = 0 then p.code[pc.toNat / 4]? else none

/-- Sign-extend an n-bit immediate to 32 bits (the hardware does this). -/
abbrev sext {n : Nat} (imm : BitVec n) : Word := imm.signExtend 32

/-! ## The semantics: one instruction -/

open Machine in
/-- Execute one instruction. This is the heart of the model: every rule in
    the RISC-V spec for these instructions, transcribed. Read each line next to
    the ISA manual and ask "is that really what the hardware does?" -/
def exec (i : Instr) (m : Machine) : Outcome :=
  let next := m.pc + 4
  match i with
  | .lui rd imm      => .running ((m.setReg rd ((imm.zeroExtend 32) <<< 12)).setPc next)
  | .addi rd rs1 imm => .running ((m.setReg rd (m.reg rs1 + sext imm)).setPc next)
  | .andi rd rs1 imm => .running ((m.setReg rd (m.reg rs1 &&& sext imm)).setPc next)
  | .sltiu rd rs1 imm =>
      .running ((m.setReg rd (if (m.reg rs1).ult (sext imm) then 1 else 0)).setPc next)
  | .slli rd rs1 sh  => .running ((m.setReg rd (m.reg rs1 <<< sh.toNat)).setPc next)
  | .srli rd rs1 sh  => .running ((m.setReg rd (m.reg rs1 >>> sh.toNat)).setPc next)
  | .add rd rs1 rs2  => .running ((m.setReg rd (m.reg rs1 + m.reg rs2)).setPc next)
  | .sub rd rs1 rs2  => .running ((m.setReg rd (m.reg rs1 - m.reg rs2)).setPc next)
  | .and rd rs1 rs2  => .running ((m.setReg rd (m.reg rs1 &&& m.reg rs2)).setPc next)
  | .or rd rs1 rs2   => .running ((m.setReg rd (m.reg rs1 ||| m.reg rs2)).setPc next)
  | .xor rd rs1 rs2  => .running ((m.setReg rd (m.reg rs1 ^^^ m.reg rs2)).setPc next)
  | .sltu rd rs1 rs2 =>
      .running ((m.setReg rd (if (m.reg rs1).ult (m.reg rs2) then 1 else 0)).setPc next)
  | .lbu rd rs1 off =>
      let a := m.reg rs1 + sext off
      if m.canRead a then .running ((m.setReg rd ((m.mem a).zeroExtend 32)).setPc next)
      else .fault (.badRead a)
  | .sb rs2 rs1 off =>
      let a := m.reg rs1 + sext off
      if m.canWrite a then .running ((m.setMem a ((m.reg rs2).truncate 8)).setPc next)
      else .fault (.badWrite a)
  | .branch c rs1 rs2 off =>
      if c.eval (m.reg rs1) (m.reg rs2) then .running (m.setPc (m.pc + sext off))
      else .running (m.setPc next)
  | .jal rd off      => .running ((m.setReg rd next).setPc (m.pc + sext off))
  | .jalr rd rs1 off => .running ((m.setReg rd next).setPc ((m.reg rs1 + sext off) &&& ~~~1))
  | .ecall =>
      if m.reg a7 = 93 then .halted (m.reg a0)       -- exit(a0)
      else .fault (.badSyscall (m.reg a7))

/-- One step: fetch, then execute. -/
def step (p : Program) (m : Machine) : Outcome :=
  match p.fetch m.pc with
  | some i => exec i m
  | none   => .fault (.badFetch m.pc)

/-- Run for at most `fuel` steps. Lean requires every function to terminate,
    so we cannot write `while (true) step();` — instead we pass a step budget.
    If the budget runs out we return `.running m` (the machine is still going).
    A `.halted` or `.fault` result is final: it can only come from the program. -/
def run (p : Program) : Nat → Machine → Outcome
  | 0,        m => .running m
  | fuel + 1, m =>
      match step p m with
      | .running m' => run p fuel m'
      | done        => done

/-! ## The process model: how a "fuzz harness" gets its input -/

/-- Where the loader puts the input buffer. -/
def inputBase : Word := 0x10000

/-- The article's bound: inputs strictly smaller than 64 MiB. -/
def maxInput : Nat := 64 * 1024 * 1024

/-- Is address `a` inside the input buffer of length `len`? -/
def inInput (len : Nat) (a : Word) : Bool :=
  decide (inputBase.toNat ≤ a.toNat ∧ a.toNat < inputBase.toNat + len)

/-- The initial machine for `LLVMFuzzerTestOneInput(data, size)`:
    `a0 = data`, `a1 = size`, pc = 0, everything else zero, and *only* the
    input bytes are readable. Nothing is writable unless a harness says so. -/
def load (input : List Byte) : Machine where
  regs := fun r => if r = a0 then inputBase
                   else if r = a1 then BitVec.ofNat 32 input.length
                   else 0
  pc := 0
  mem := fun a => if inInput input.length a then input[(a - inputBase).toNat]?.getD 0 else 0
  canRead := inInput input.length
  canWrite := fun _ => false

/-- **The spec shape from the article**: started on this input, the program
    reaches `exit` within some finite number of steps, and so never faults
    (a fault would have stopped `run` with `.fault`, not `.halted`). -/
def ExitsCleanly (p : Program) (m : Machine) : Prop :=
  ∃ fuel code, run p fuel m = .halted code

/-- Stronger: it exits, and with a specific code. -/
def ExitsWith (p : Program) (m : Machine) (code : Word) : Prop :=
  ∃ fuel, run p fuel m = .halted code

/-! ## Display helpers (not part of the model: no theorem mentions them) -/

/-- Pretty-print an outcome (the machine has functions inside, so no `Repr`). -/
def Outcome.show : Outcome → String
  | .running m => s!"still running at pc={m.pc.toNat}"
  | .halted c  => s!"exit({c.toNat})"
  | .fault f   => s!"CRASH: {repr f}"

/-- Run a program on an input and report the exit code, if it exits. -/
def exitCode (p : Program) (input : List Byte) (fuel : Nat := 10000) : Option Nat :=
  match run p fuel (load input) with
  | .halted c => some c.toNat
  | _         => none

end Metal
