import Metal.S01_LeanForC

/-!
# Exercises — Stage 1: Lean as a programming language

How this file works:
* Replace each `sorry` with an implementation.
* Under each exercise are `#guard` tests, commented out. When you've written
  the function, **uncomment its tests** (delete the leading `-- `). A failing
  `#guard` is a compile error that shows you the expression that was false.
* Check your work: `lake build Exercises.S01_LeanForC`, or just watch the
  editor. When there are no errors and no `sorry` warnings, you're done.
* Stuck? `Solutions/S01_LeanForC.lean`. Try for 15 minutes first.

Difficulty: ★ warm-up · ★★ real work · ★★★ think first.
-/

namespace Metal.S01.Ex
open Metal.S01

/-- Helper: the bytes of an ASCII string. -/
def bytesOf (s : String) : List Byte := s.toList.map (fun c => BitVec.ofNat 8 c.toNat)

/-! ## E1.1 ★ XOR checksum
XOR all the bytes together (start from 0). Hint: `List.foldl` and `^^^`. -/
def xorAll (xs : List Byte) : Byte := sorry

-- #guard xorAll [] == 0
-- #guard xorAll [0x0F, 0xF0] == 0xFF
-- #guard xorAll [0xAA, 0x55, 0xAA] == 0x55

/-! ## E1.2 ★ Count the bytes that satisfy a predicate
Write it with explicit recursion (pattern match on `[]` and `x :: xs`), not a
library function: you'll prove things about functions like this in Stage 2. -/
def countIf (p : Byte → Bool) (xs : List Byte) : Nat := sorry

-- #guard countIf (· == 0) [0, 1, 0, 2] == 2
-- #guard countIf (fun b => b.toNat ≥ 0x80) [0x80, 0x7F, 0xFF] == 2

/-! ## E1.3 ★★ Fletcher-16
Two running sums mod 255: for each byte b,
`s1 := (s1 + b) % 255; s2 := (s2 + s1) % 255`; result is `s2 * 256 + s1`.
Work in `Nat` (use `b.toNat`). A `foldl` over a pair `(s1, s2)` is natural;
`let (a, b) := pair` destructures. -/
def fletcher16 (xs : List Byte) : Nat := sorry

-- #guard fletcher16 (bytesOf "abcde") == 0xC8F0
-- #guard fletcher16 (bytesOf "abcdef") == 0x2057
-- #guard fletcher16 (bytesOf "abcdefgh") == 0x0627

/-! ## E1.4 ★★ Parse a decimal byte, safely
Accept one or more ASCII digits whose value is ≤ 255; leading zeros are fine.
Reject (return `none`) empty strings, non-digits, and overflow — *including*
inputs like "99999999999999999999" (think about when you can stop early;
`Nat` won't overflow, but a C version would). Hint: a helper with an
accumulator; `Char.isDigit`; `c.toNat - '0'.toNat`. You can declare a helper
inside the definition with `where`, or just write a separate `def` above. -/
def parseU8 (s : List Char) : Option Byte := sorry

-- #guard parseU8 "255".toList == some 255
-- #guard parseU8 "007".toList == some 7
-- #guard parseU8 "256".toList == none
-- #guard parseU8 "99999999999999999999".toList == none
-- #guard parseU8 "".toList == none
-- #guard parseU8 "1a".toList == none

/-! ## E1.5 ★★ A stack machine (a preview of Stage 5)
An interpreter where "crash" (stack underflow) is `none`. The stack is a
`List Nat` with the top at the head. `add` pops `a` then `b` and pushes
`b + a`; `mul` likewise; `dup` duplicates the top; `swap` swaps the top two;
`drop` discards the top. Any op without enough operands returns `none`.
`runOps` runs a list of ops left to right and stops at the first `none`. -/
inductive Op where
  | push (n : Nat)
  | add
  | mul
  | dup
  | swap
  | drop
  deriving Repr

def Op.exec (op : Op) (s : List Nat) : Option (List Nat) := sorry

def runOps (ops : List Op) (s : List Nat) : Option (List Nat) := sorry

-- #guard runOps [.push 2, .push 3, .add, .dup, .mul] [] == some [25]
-- #guard runOps [.push 1, .add] [] == none
-- #guard runOps [.push 1, .push 2, .swap, .drop] [] == some [2]

/-! ## E1.6 ★★ The capstone harness as a spec
Write, in plain Lean, what the Stage 7 C harness *should* return: input
`[n, payload...]`; if the payload has at least `n` bytes, the sum of the first
`n` payload bytes; otherwise (or on empty input) 0. This is the "reference
implementation" a differential spec compares against. -/
def harnessSpec (input : List Byte) : Nat := sorry

-- #guard harnessSpec [] == 0
-- #guard harnessSpec [2, 10, 20] == 30
-- #guard harnessSpec [2, 10, 20, 99] == 30
-- #guard harnessSpec [3, 10, 20] == 0
-- #guard harnessSpec [1] == 0

end Metal.S01.Ex
