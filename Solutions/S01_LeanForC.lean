import Metal.S01_LeanForC

/-! # Solutions — Stage 1 -/

namespace Metal.S01.Ex
open Metal.S01

/-- Helper: the bytes of an ASCII string. -/
def bytesOf (s : String) : List Byte := s.toList.map (fun c => BitVec.ofNat 8 c.toNat)

/-! ## E1.1 XOR checksum -/
def xorAll (xs : List Byte) : Byte := xs.foldl (· ^^^ ·) 0

#guard xorAll [] == 0
#guard xorAll [0x0F, 0xF0] == 0xFF
#guard xorAll [0xAA, 0x55, 0xAA] == 0x55

/-! ## E1.2 Count the bytes that satisfy a predicate -/
def countIf (p : Byte → Bool) : List Byte → Nat
  | []      => 0
  | x :: xs => (if p x then 1 else 0) + countIf p xs

#guard countIf (· == 0) [0, 1, 0, 2] == 2
#guard countIf (fun b => b.toNat ≥ 0x80) [0x80, 0x7F, 0xFF] == 2

/-! ## E1.3 Fletcher-16 -/
def fletcher16 (xs : List Byte) : Nat :=
  let (s1, s2) := xs.foldl (fun (s1, s2) b =>
    let s1' := (s1 + b.toNat) % 255
    (s1', (s2 + s1') % 255)) (0, 0)
  s2 * 256 + s1

#guard fletcher16 (bytesOf "abcde") == 0xC8F0
#guard fletcher16 (bytesOf "abcdef") == 0x2057
#guard fletcher16 (bytesOf "abcdefgh") == 0x0627

/-! ## E1.4 Parse a decimal byte -/
def parseU8 (s : List Char) : Option Byte :=
  if s.isEmpty then none else go s 0
where
  go : List Char → Nat → Option Byte
    | [],      acc => if acc ≤ 255 then some (BitVec.ofNat 8 acc) else none
    | c :: cs, acc =>
      if c.isDigit && acc ≤ 255 then go cs (acc * 10 + (c.toNat - '0'.toNat)) else none

#guard parseU8 "255".toList == some 255
#guard parseU8 "007".toList == some 7
#guard parseU8 "256".toList == none
#guard parseU8 "99999999999999999999".toList == none
#guard parseU8 "".toList == none
#guard parseU8 "1a".toList == none

/-! ## E1.5 A stack machine — an interpreter where "crash" is `none` -/
inductive Op where
  | push (n : Nat)
  | add
  | mul
  | dup
  | swap
  | drop
  deriving Repr

def Op.exec : Op → List Nat → Option (List Nat)
  | .push n, s           => some (n :: s)
  | .add,    a :: b :: s => some ((b + a) :: s)
  | .mul,    a :: b :: s => some ((b * a) :: s)
  | .dup,    a :: s      => some (a :: a :: s)
  | .swap,   a :: b :: s => some (b :: a :: s)
  | .drop,   _ :: s      => some s
  | _,       _           => none          -- stack underflow: the "crash"

def runOps : List Op → List Nat → Option (List Nat)
  | [],        s => some s
  | op :: ops, s =>
    match op.exec s with
    | none    => none
    | some s' => runOps ops s'

#guard runOps [.push 2, .push 3, .add, .dup, .mul] [] == some [25]
#guard runOps [.push 1, .add] [] == none
#guard runOps [.push 1, .push 2, .swap, .drop] [] == some [2]

/-! ## E1.6 The capstone harness, as a spec: what should it return? -/
def harnessSpec (input : List Byte) : Nat :=
  match input with
  | []        => 0
  | n :: rest => if n.toNat < input.length then (rest.take n.toNat |>.map (·.toNat)).sum else 0

#guard harnessSpec [] == 0
#guard harnessSpec [2, 10, 20] == 30
#guard harnessSpec [2, 10, 20, 99] == 30
#guard harnessSpec [3, 10, 20] == 0
#guard harnessSpec [1] == 0

end Metal.S01.Ex
