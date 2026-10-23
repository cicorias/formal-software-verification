import Lean

/-!
# A tiny proof auditor

`#assert_axioms foo` fails to compile unless `foo` depends only on Lean's
three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
That rules out `sorry` (`sorryAx`), any user `axiom`, `native_decide`, and
`bv_decide` (both add `…_native…` axioms that trust the compiler).

Used by `Lab/Audit.lean` and `tools/proof_guard.py` (Stage 9).
-/

open Lean Elab Command

/-- The axioms a proof may use. -/
def Metal.Guard.standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

elab "#assert_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter (fun a => !Metal.Guard.standardAxioms.contains a)
  if bad.isEmpty then
    logInfo m!"axioms OK: {n} uses only {axs.toList}"
  else
    throwError m!"REJECTED: {n} depends on non-standard axioms {bad.toList}"
