import Lab.Spec
import Lab.Proof
import Metal.Guard

/-!
# Lab audit — FROZEN

Two checks, enforced by the Lean compiler:
1. `Lab.main` proves *exactly* the frozen statement `Lab.Statement`
   (not a weaker one the agent wrote itself);
2. it uses only the standard axioms (no `sorry`, no `axiom`, no native code).

This file gives fast feedback, but it is NOT the final word: it imports
`Lab.Proof`, so it is parsed with whatever syntax the proof's imports define.
The decisive checks are `tools/AxCheck.lean` (run as a separate program that
loads the compiled proof) and `leanchecker` (kernel replay); see
`tools/proof_guard.py`.
-/

example : Lab.Statement := Lab.main

#assert_axioms Lab.main
