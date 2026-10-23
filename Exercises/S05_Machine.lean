import Metal.S05_Playground

/-!
# Exercises — Stage 5: the machine

Tools: `exitCode prog input`, `(run prog fuel (load input)).show`,
`trace prog input`, `IO.println prog.disasm` (all in `S05_Playground.lean`).
Put an `#eval` anywhere to poke at things.

Check: `lake build Exercises.S05_Machine`.
-/

namespace Metal.S05Ex
open Metal Reg Instr Machine

/-! ## E5.1 ★ Predict, then check
For each program, write down the exit code you expect *before* running
anything. Then replace the `0` with your prediction and `sorry` with `rfl`.
If `rfl` fails, your prediction was wrong: work out why (`trace` helps). -/

def p1 : Program := ⟨[li a0 5, addi a0 a0 (-6), li a7 93, ecall]⟩
theorem e5_1a : exitCode p1 [] = some 0 := by sorry

def p2 : Program := ⟨[li zero 7, mv a0 zero, li a7 93, ecall]⟩
theorem e5_1b : exitCode p2 [] = some 0 := by sorry

def p3 : Program := ⟨[li a0 1, li a1 (-1), sltu a0 a1 a0, li a7 93, ecall]⟩
theorem e5_1c : exitCode p3 [] = some 0 := by sorry

/-- Careful: `0x800` is a 12-bit immediate. -/
def p4 : Program := ⟨[lui a0 1, addi a0 a0 0x800, li a7 93, ecall]⟩
theorem e5_1d : exitCode p4 [] = some 0 := by sorry

def p5 : Program := ⟨[li t0 13, jalr zero t0 0, li a0 1, li a0 2, li a7 93, ecall]⟩
theorem e5_1e : exitCode p5 [] = some 0 := by sorry

def p6 : Program := ⟨[li a0 0, li a1 5, addi a0 a0 3, addi a1 a1 (-1), bnez a1 (-8), li a7 93, ecall]⟩
theorem e5_1f : exitCode p6 [] = some 0 := by sorry

/-! ## E5.2 ★★ Transcribe a compiled function
`clang --target=riscv32-unknown-elf -march=rv32i -O1` on
```c
uint32_t count_zeros(const uint8_t *p, size_t len) {
  uint32_t c = 0;
  for (size_t i = 0; i < len; i++) c += (p[i] == 0);
  return c;
}
```
gives
```
count_zeros:
        li      a2, 0
        beqz    a1, .LBB0_3
        add     a1, a0, a1
.LBB0_2:
        lbu     a3, 0(a0)
        seqz    a3, a3
        addi    a0, a0, 1
        add     a2, a2, a3
        bne     a0, a1, .LBB0_2
.LBB0_3:
        mv      a0, a2
        ret
```
Write `countZerosProg`: the same three-instruction `_start` stub as
`sumProg` (`jal ra 12; li a7 93; ecall`), then this body. You must compute
the branch offsets yourself: an offset is (target address − branch address),
in bytes. Annotate each line with its address, like `sumProg` does.
Then make the tests pass (uncomment, `rfl`). -/

def countZerosProg : Program := sorry

-- theorem e5_2a : exitCode countZerosProg [0, 1, 0, 0] = some 3 := by rfl
-- theorem e5_2b : exitCode countZerosProg [] = some 0 := by rfl
-- theorem e5_2c : exitCode countZerosProg [5, 6] = some 0 := by rfl

/-! ## E5.3 ★★ A loop with a branch inside
```c
uint32_t max_byte(const uint8_t *p, size_t len) {
  uint32_t m = 0;
  for (size_t i = 0; i < len; i++) if (p[i] > m) m = p[i];
  return m;
}
```
```
max_byte:
        li      a2, 0
        beqz    a1, .LBB1_5
        add     a1, a0, a1
        j       .LBB1_3
.LBB1_2:
        addi    a0, a0, 1
        beq     a0, a1, .LBB1_5
.LBB1_3:
        lbu     a3, 0(a0)
        bltu    a3, a2, .LBB1_2
        mv      a2, a3
        j       .LBB1_2
.LBB1_5:
        mv      a0, a2
        ret
```
(`j label` is `jal x0, label`; RV-lite has `j` as a pseudo-instruction.) -/

def maxByteProg : Program := sorry

-- theorem e5_3a : exitCode maxByteProg [3, 200, 7] = some 200 := by rfl
-- theorem e5_3b : exitCode maxByteProg [] = some 0 := by rfl
-- theorem e5_3c : exitCode maxByteProg [255] = some 255 := by rfl

/-! ## E5.4 ★ Crash it
`lastByteProg` (in the playground) has a bug. Find an input that makes it
fault, and state exactly how: replace `[9]`, the `5` and the fault below,
then prove it with `rfl`. -/
theorem e5_4 : run lastByteProg 5 (load [9]) = .fault (.badRead 0) := by
  sorry

end Metal.S05Ex
