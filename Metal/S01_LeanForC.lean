/-!
# Stage 1 — Lean 4 for C programmers

Lean is two things in one file:

1. a pure functional programming language (think: C without pointers,
   without mutation, without `while`, with tagged unions done right), and
2. a proof checker for statements *about* those programs.

This stage is only (1). You can't state anything about code you can't write.

How to use this file: open it in VS Code with the Lean 4 extension. Every
`#eval` shows its result in the infoview (the panel on the right) when your
cursor is on it. Change things. Break things. The feedback loop is ~instant.
Read `docs/01-lean-for-c.md` for the narrative.
-/

namespace Metal.S01

/-! ## 1. Values, functions, `#eval` -/

def answer : Nat := 42
#eval answer                      -- 42

/-- Function application is juxtaposition: `add3 1 2 3`, not `add3(1, 2, 3)`. -/
def add3 (a b c : Nat) : Nat := a + b + c
#eval add3 1 2 3                  -- 6

/-! ## 2. Numbers: the most important table in this course

| Lean type   | C analogue            | Arithmetic                     |
|-------------|-----------------------|--------------------------------|
| `Nat`       | none: unbounded ≥ 0   | exact; `3 - 5 = 0` (truncates!) |
| `Int`       | none: unbounded       | exact                          |
| `UInt8/32`  | `uint8_t`/`uint32_t`  | mod 2^n, fast, *for programs*  |
| `BitVec n`  | `uintN_t`, any n      | mod 2^n, *for proofs*          |
| `Fin n`     | an index known `< n`  | mod n                          |

Specs talk in `Nat` ("the buffer has `len` bytes"). Machines compute in
`BitVec 32`. **Overflow bugs live exactly in the gap between the two**, and
Stage 4 is about crossing it safely. -/

#eval (255 : Nat) + 1        -- 256
#eval (255 : UInt8) + 1      -- 0    (wraps, like uint8_t)
#eval (255#8) + 1            -- 0#8  (`255#8` = the 8-bit bitvector 255)
#eval (3 : Nat) - 5          -- 0    (!) Nat subtraction stops at zero
#eval (3 : Int) - 5          -- -2
#eval (0xFF#8).toNat         -- 255  (BitVec → Nat: the "meaning" of the bits)
#eval BitVec.ofNat 8 300     -- 44#8 (Nat → BitVec: reduce mod 2^8)

/-! ## 3. `struct` → `structure` -/

structure Point where
  x : Int
  y : Int
  deriving Repr

def origin : Point := { x := 0, y := 0 }

/-- Methods are just functions in the type's namespace; `p.add q` means `Point.add p q`. -/
def Point.add (p q : Point) : Point := { x := p.x + q.x, y := p.y + q.y }

#eval origin.add ⟨3, 4⟩            -- ⟨3, 4⟩ is an anonymous constructor: Point.mk 3 4

/-- There is no assignment. `{ p with x := ... }` builds a *new* struct
    (and the compiler will happily do it in place when `p` isn't shared). -/
def moveRight (p : Point) : Point := { p with x := p.x + 1 }

/-! ## 4. `enum` and tagged unions → `inductive`

A C tagged union is `struct { enum tag; union { ... } u; }` and nothing stops
you reading `u.rect.w` when the tag says `CIRCLE`. An `inductive` makes that
impossible: the only way to get at the fields is to `match` on the tag. -/

inductive Shape where
  | circle (r : Nat)
  | rect   (w h : Nat)
  deriving Repr

/-- `match` is a `switch` that must be exhaustive. Delete a case and this
    fails to compile. (Try it.) -/
def Shape.area : Shape → Nat
  | .circle r => 3 * r * r          -- integer π; don't ship it
  | .rect w h => w * h

#eval (Shape.rect 3 4).area         -- 12

/-! ## 5. `NULL` and error codes → `Option` / `Except`

`Option α` is either `none` or `some a`. You cannot use the `a` without
handling `none`: there is no "forgot to check for NULL". -/

def safeDiv (a b : Nat) : Option Nat :=
  if b = 0 then none else some (a / b)

#eval safeDiv 10 2                  -- some 5
#eval safeDiv 10 0                  -- none

def describe (r : Option Nat) : String :=
  match r with
  | none   => "error"
  | some v => s!"ok: {v}"            -- s!"..." is string interpolation

/-- `Except ε α` carries an error *value*, like returning `-EINVAL`. -/
def parseDigit (c : Char) : Except String Nat :=
  if c.isDigit then .ok (c.toNat - '0'.toNat) else .error s!"not a digit: {c}"

#eval parseDigit '7'                -- Except.ok 7
#eval parseDigit 'x'                -- Except.error "not a digit: x"

/-! ## 6. Loops → recursion

`List α` is an immutable singly-linked list: `[]` (like NULL) or `x :: xs`
(a cons cell). Recursion over it is the `for` loop. -/

def sumList : List Nat → Nat
  | []      => 0
  | x :: xs => x + sumList xs

#eval sumList [1, 2, 3, 4]          -- 10

/-- With an accumulator, the recursive call is the last thing that happens
    (a tail call) and the compiler emits a loop: no stack growth. This is the
    version you'd actually write in C. Stage 2 *proves* the two agree. -/
def sumAcc (acc : Nat) : List Nat → Nat
  | []      => acc
  | x :: xs => sumAcc (acc + x) xs

#eval sumAcc 0 [1, 2, 3, 4]         -- 10

/- Library functions do the same thing; `foldl` is the canonical C-style loop:
   `acc = init; for (x in xs) acc = f(acc, x); return acc;` -/
#eval [1, 2, 3, 4].foldl (· + ·) 0  -- 10   (`(· + ·)` is `fun a b => a + b`)

/-! ## 7. Every function terminates (and why a prover cares)

Lean rejects `def spin (n : Nat) : Nat := spin n`. If it allowed it,
`def bogus : False := bogus` would be a "proof" of `False`, and then
everything would be provable. Logic and infinite loops don't mix.

So how do we write a CPU interpreter, whose whole job is to loop until the
program exits? We give it **fuel**: a step budget that goes down by one each
step. You'll see this in Stage 5; it's also how the article's models work.

Lean proves termination automatically when the recursion is on a smaller
piece of the input (as above), or when it can find a decreasing measure: -/

def countdown (n : Nat) : List Nat :=
  if n = 0 then [0] else n :: countdown (n - 1)   -- Lean figures out n - 1 < n here

#eval countdown 5                   -- [5, 4, 3, 2, 1, 0]

/-! ## 8. Bytes and buffers

A C `(const uint8_t *data, size_t size)` is, in a spec, a `List (BitVec 8)`.
No pointer, no separate length that can disagree with the data, no way to
read past the end: `xs[i]?` returns `none` out of range, and `xs[i]` requires
a *proof* that `i < xs.length`. -/

abbrev Byte := BitVec 8

def sample : List Byte := [0x03, 0x41, 0x42, 0x43]

#eval sample[1]?                    -- some 0x41#8
#eval sample[9]?                    -- none
#eval sample.length                 -- 4

/-! ## 9. Worked example: the Stage 7 harness, as a *spec*

The capstone parses `[n][n bytes of payload]`. Here is that logic written
the way specs are written: total, no pointers, no off-by-one possible. -/

/-- Return the payload, or `none` if the record is malformed. -/
def parseRecord : List Byte → Option (List Byte)
  | []        => none
  | n :: rest => if n.toNat ≤ rest.length then some (rest.take n.toNat) else none

#eval parseRecord sample            -- some [0x41#8, 0x42#8, 0x43#8]
#eval parseRecord [0x05, 0x41]      -- none: claims 5 bytes, has 1
#eval parseRecord [0x01]            -- none: the input that crashes the C version

/-- The checksum the C harness computes, as a spec. -/
def payloadSum (input : List Byte) : Nat :=
  match parseRecord input with
  | none    => 0
  | some ps => (ps.map (·.toNat)).sum

#eval payloadSum sample             -- 198 = 0x41 + 0x42 + 0x43

/-! ## 10. `IO`: Lean is a real language

`#eval` can run effects. A Lake project can also build a native executable
(`lean_exe` in `lakefile.toml`) — we don't need one in this course. -/

def greet : IO Unit := do
  let xs := [1, 2, 3]
  for x in xs do                    -- `do` notation gives you imperative syntax
    IO.println s!"x = {x}"          -- (it desugars to the recursion you saw above)

#eval greet

end Metal.S01
