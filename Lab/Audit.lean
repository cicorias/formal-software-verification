import Lab.Spec
import Lab.Proof
import Metal.Guard

/-!
# Lab audit — FROZEN

Two checks, both enforced by the Lean compiler:
1. `Lab.main` proves *exactly* the frozen statement `Lab.Statement`
   (not a weaker one the agent wrote itself);
2. it uses only the standard axioms (no `sorry`, no `axiom`, no native code).
-/

example : Lab.Statement := Lab.main

#assert_axioms Lab.main
