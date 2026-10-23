import Metal.S05_Machine

/-!
# Stage 5b — Driving the machine

`S05_Machine.lean` defined the CPU. Here we *use* it, the way you'd use a
simulator or `gdb`: load an input, run, look at the result, single-step.
Everything here is executable (`#eval`) and some of it is checked by the
kernel (`example … := by rfl`): a test that lives inside the prover.
-/

namespace Metal
open Reg Instr Machine

/-! ## A disassembler and a single-stepping tracer (your `objdump` and `gdb`) -/

/-- Show a word as hex. -/
def hex (w : Word) : String := "0x" ++ String.ofList (Nat.toDigits 16 w.toNat)

def regName (r : Reg) : String :=
  #["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3",
    "a4", "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
    "t3", "t4", "t5", "t6"][r.val]!

def Cond.mnemonic : Cond → String
  | .eq => "beq" | .ne => "bne" | .lt => "blt" | .ge => "bge" | .ltu => "bltu" | .geu => "bgeu"

/-- Print an instruction the way `objdump -d` would (immediates as signed decimals). -/
def Instr.asm : Instr → String
  | .lui rd imm         => s!"lui {regName rd}, {imm.toNat}"
  | .addi rd rs imm     => s!"addi {regName rd}, {regName rs}, {imm.toInt}"
  | .andi rd rs imm     => s!"andi {regName rd}, {regName rs}, {imm.toInt}"
  | .sltiu rd rs imm    => s!"sltiu {regName rd}, {regName rs}, {imm.toInt}"
  | .slli rd rs sh      => s!"slli {regName rd}, {regName rs}, {sh.toNat}"
  | .srli rd rs sh      => s!"srli {regName rd}, {regName rs}, {sh.toNat}"
  | .add rd a b         => s!"add {regName rd}, {regName a}, {regName b}"
  | .sub rd a b         => s!"sub {regName rd}, {regName a}, {regName b}"
  | .and rd a b         => s!"and {regName rd}, {regName a}, {regName b}"
  | .or rd a b          => s!"or {regName rd}, {regName a}, {regName b}"
  | .xor rd a b         => s!"xor {regName rd}, {regName a}, {regName b}"
  | .sltu rd a b        => s!"sltu {regName rd}, {regName a}, {regName b}"
  | .lbu rd rs off      => s!"lbu {regName rd}, {off.toInt}({regName rs})"
  | .sb rs2 rs1 off     => s!"sb {regName rs2}, {off.toInt}({regName rs1})"
  | .branch c a b off   => s!"{c.mnemonic} {regName a}, {regName b}, {off.toInt}"
  | .jal rd off         => s!"jal {regName rd}, {off.toInt}"
  | .jalr rd rs off     => s!"jalr {regName rd}, {off.toInt}({regName rs})"
  | .ecall              => "ecall"

/-- `objdump -d`: list a program with addresses. -/
def Program.disasm (p : Program) : String :=
  String.intercalate "\n" <| p.code.zipIdx.map fun (i, k) => s!"{hex (BitVec.ofNat 32 (4 * k))}:  {i.asm}"

/-- Execute up to `n` steps, printing pc, the instruction, and a0–a3 after each. -/
def trace (p : Program) (input : List Byte) (n : Nat := 50) : IO Unit := do
  let mut m := load input
  for _ in [0:n] do
    let ins := match p.fetch m.pc with | some i => i.asm | none => "<no instruction>"
    match step p m with
    | .running m' =>
      IO.println s!"{hex m.pc}: {ins}   ⟹ a0={hex (m'.reg a0)} a1={hex (m'.reg a1)} a2={hex (m'.reg a2)} a3={hex (m'.reg a3)}"
      m := m'
    | .halted c => IO.println s!"{hex m.pc}: {ins}   ⟹ exit({c.toNat})"; return
    | .fault f  => IO.println s!"{hex m.pc}: {ins}   ⟹ CRASH {repr f}"; return
  IO.println "(step budget exhausted)"

/-! ## Sign extension: where small immediates become big numbers

`addi a0, x0, -1` has a 12-bit immediate `0xFFF`. The CPU sign-extends it,
so a0 becomes 0xFFFFFFFF — not 0xFFF. The exit code shows the full word
(our toy `exit` keeps 32 bits; real Linux would keep the low 8). -/

def minusOne : Program := ⟨[
  li a0 (-1),          -- a0 = sext(0xFFF) = 0xFFFFFFFF
  li a7 93,
  ecall
]⟩

#eval exitCode minusOne []                 -- some 4294967295
example : exitCode minusOne [] = some 0xFFFFFFFF := by rfl   -- kernel-checked test

/-! `lbu` zero-extends the byte; a signed `lb` (which RV-lite doesn't have)
would sign-extend. Mixing them up is the RISC-V version of the C bug
`char c = buf[i]; if (c > 127) ...` (never true when `char` is signed). -/

def firstByte : Program := ⟨[
  lbu a0 a0 0,         -- a0 = zext(data[0])
  li a7 93,
  ecall
]⟩

#eval exitCode firstByte [0xFF]            -- some 255 (not 4294967295)

/-! ## A real clang function, and the input that kills it

```c
uint32_t last_byte(const uint8_t *p, size_t len) { return p[len - 1]; }
```
clang -O1 (riscv32):
```
last_byte:  add a0, a0, a1
            lbu a0, -1(a0)
            ret
```
Nothing checks `len > 0`. With `len = 0` it reads `p[-1]`. -/

def lastByteProg : Program := ⟨[
  /- 0x00 _start: -/ jal ra 12,
  /- 0x04 -/         li a7 93,
  /- 0x08 -/         ecall,
  /- 0x0c last_byte: -/ add a0 a0 a1,
  /- 0x10 -/         lbu a0 a0 (-1),     -- offset -1: sign-extended 12-bit immediate
  /- 0x14 -/         ret
]⟩

#eval IO.println lastByteProg.disasm
#eval (run lastByteProg 100 (load [1, 2, 3])).show   -- exit(3)
#eval (run lastByteProg 100 (load [])).show          -- CRASH: badRead 0xffff (= inputBase - 1)
#eval trace lastByteProg [10, 20, 30]

/-! ## Tests vs. theorems

`by rfl` on a concrete input is a *test*: the kernel runs the program and
compares. It's exactly as strong as a fuzzer finding no crash on that one
input — no more. Stage 6 is about the leap from "this input" to "all inputs". -/

example : exitCode lastByteProg [1, 2, 3] = some 3 := by rfl
example : run lastByteProg 5 (load []) = .fault (.badRead 0xFFFF) := by rfl

end Metal
