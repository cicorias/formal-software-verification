import Metal.S05_Playground

/-! # Solutions — Stage 5 -/

namespace Metal.S05Ex
open Metal Reg Instr Machine

/-! ## E5.1 Predict the exit code -/

/-- 5 + sext(-6) = 0xFFFFFFFF -/
def p1 : Program := ⟨[li a0 5, addi a0 a0 (-6), li a7 93, ecall]⟩
theorem e5_1a : exitCode p1 [] = some 4294967295 := by rfl

/-- x0 ignores writes. -/
def p2 : Program := ⟨[li zero 7, mv a0 zero, li a7 93, ecall]⟩
theorem e5_1b : exitCode p2 [] = some 0 := by rfl

/-- `sltu` is unsigned: 0xFFFFFFFF <u 1 is false. (A signed `slt` would say true.) -/
def p3 : Program := ⟨[li a0 1, li a1 (-1), sltu a0 a1 a0, li a7 93, ecall]⟩
theorem e5_1c : exitCode p3 [] = some 0 := by rfl

/-- `lui` then `addi` with 0x800: the 12-bit immediate is sign-extended to -2048,
    so 0x1000 + (-2048) = 2048. This is why assemblers adjust `%hi` by one
    when bit 11 of `%lo` is set. -/
def p4 : Program := ⟨[lui a0 1, addi a0 a0 0x800, li a7 93, ecall]⟩
theorem e5_1d : exitCode p4 [] = some 2048 := by rfl

/-- `jalr` clears bit 0 of the target: 13 becomes 12, skipping `li a0 1`. -/
def p5 : Program := ⟨[li t0 13, jalr zero t0 0, li a0 1, li a0 2, li a7 93, ecall]⟩
theorem e5_1e : exitCode p5 [] = some 2 := by rfl

/-- A backward branch: five iterations of += 3. -/
def p6 : Program := ⟨[li a0 0, li a1 5, addi a0 a0 3, addi a1 a1 (-1), bnez a1 (-8), li a7 93, ecall]⟩
theorem e5_1f : exitCode p6 [] = some 15 := by rfl

/-! ## E5.2 Transcribe `count_zeros` -/
def countZerosProg : Program := ⟨[
  /- 0x00 _start: -/ jal ra 12,
  /- 0x04 -/         li a7 93,
  /- 0x08 -/         ecall,
  /- 0x0c count_zeros: -/ li a2 0,
  /- 0x10 -/         beqz a1 28,         -- → .LBB0_3 (0x2c)
  /- 0x14 -/         add a1 a0 a1,
  /- 0x18 .LBB0_2: -/ lbu a3 a0 0,
  /- 0x1c -/         seqz a3 a3,
  /- 0x20 -/         addi a0 a0 1,
  /- 0x24 -/         add a2 a2 a3,
  /- 0x28 -/         bne a0 a1 (-16),    -- → .LBB0_2 (0x18)
  /- 0x2c .LBB0_3: -/ mv a0 a2,
  /- 0x30 -/         ret
]⟩

theorem e5_2a : exitCode countZerosProg [0, 1, 0, 0] = some 3 := by rfl
theorem e5_2b : exitCode countZerosProg [] = some 0 := by rfl
theorem e5_2c : exitCode countZerosProg [5, 6] = some 0 := by rfl

/-! ## E5.3 Transcribe `max_byte` -/
def maxByteProg : Program := ⟨[
  /- 0x00 _start: -/ jal ra 12,
  /- 0x04 -/         li a7 93,
  /- 0x08 -/         ecall,
  /- 0x0c max_byte: -/ li a2 0,
  /- 0x10 -/         beqz a1 36,         -- → .LBB1_5 (0x34)
  /- 0x14 -/         add a1 a0 a1,
  /- 0x18 -/         j 12,               -- → .LBB1_3 (0x24)
  /- 0x1c .LBB1_2: -/ addi a0 a0 1,
  /- 0x20 -/         beq a0 a1 20,       -- → .LBB1_5 (0x34)
  /- 0x24 .LBB1_3: -/ lbu a3 a0 0,
  /- 0x28 -/         bltu a3 a2 (-12),   -- → .LBB1_2 (0x1c)
  /- 0x2c -/         mv a2 a3,
  /- 0x30 -/         j (-20),            -- → .LBB1_2 (0x1c)
  /- 0x34 .LBB1_5: -/ mv a0 a2,
  /- 0x38 -/         ret
]⟩

theorem e5_3a : exitCode maxByteProg [3, 200, 7] = some 200 := by rfl
theorem e5_3b : exitCode maxByteProg [] = some 0 := by rfl
theorem e5_3c : exitCode maxByteProg [255] = some 255 := by rfl

/-! ## E5.4 Crash it -/
theorem e5_4 : run lastByteProg 5 (load []) = .fault (.badRead 0xFFFF) := by rfl

end Metal.S05Ex
