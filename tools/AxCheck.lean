import Lean

/-!
# axcheck — an audit that the audited code can't steer

    lake env lean --run tools/AxCheck.lean <Module> <decl>[:<ExpectedTypeConst>] ...

(`lean --run` interprets `main`; nothing is linked. `lake env` puts the
project's compiled modules on the search path.)

Loads the *compiled* module `<Module>` (and everything it imports) at run
time, then for each `decl`:

* if `:<ExpectedTypeConst>` is given, checks that `decl`'s type is exactly
  that constant (e.g. `Lab.main:Lab.Statement`);
* walks every definition `decl` depends on, transitively, and fails if any
  of them is an axiom other than `propext`, `Classical.choice`, `Quot.sound`.

Why a separate executable instead of `#print axioms` in a `.lean` file? A
`.lean` file that imports the code under audit is *parsed with that code's
syntax extensions*: an imported `macro_rules` or `elab_rules` can change
what `example : Statement := main` or `#print axioms main` means. This
program is compiled without importing any of the audited code, so nothing
the audited code defines can affect how this program is read. And it does
its own dependency walk rather than trusting the per-module axiom cache
stored in the `.olean` files.

Pair it with `leanchecker`, which re-runs every declaration through the
kernel (catching declarations added to the environment without checking).
-/

open Lean

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- All axioms that `root` depends on, found by walking types and values. -/
def axiomsOf (env : Environment) (root : Name) : Except String (List Name) := Id.run do
  let mut seen : NameSet := {}
  let mut todo : List Name := [root]
  let mut axs : List Name := []
  let mut fuel := 10000000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => return .ok axs
    | c :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      match env.find? c with
      | none => return .error s!"unknown constant {c}"
      | some info =>
        if info.isUnsafe then return .error s!"{c} is unsafe"
        if let .axiomInfo _ := info then axs := c :: axs
        let mut deps : Array Name := info.type.getUsedConstants
        if let some v := info.value? (allowOpaque := true) then
          deps := deps ++ v.getUsedConstants
        if let .recInfo r := info then
          for rl in r.rules do
            deps := deps ++ (RecursorRule.rhs rl).getUsedConstants
        todo := deps.toList ++ todo
  return .error "dependency walk did not terminate"

def checkOne (env : Environment) (spec : String) : IO Bool := do
  let (declStr, tyStr?) := match spec.splitOn ":" with
    | [d, t] => (d, some t)
    | _      => (spec, none)
  let decl := declStr.toName
  let some info := env.find? decl
    | IO.println s!"REJECTED: {decl} not found"; return false
  if let some tyStr := tyStr? then
    let expected := mkConst tyStr.toName
    unless info.type == expected do
      IO.println s!"REJECTED: {decl} has type {info.type}, expected exactly {expected}"
      return false
  match axiomsOf env decl with
  | .error e => IO.println s!"REJECTED: {e}"; return false
  | .ok axs =>
    let bad := axs.filter (fun a => !standardAxioms.contains a)
    if bad.isEmpty then
      IO.println s!"axioms OK: {decl} uses only {axs.reverse}"
      return true
    else
      IO.println s!"REJECTED: {decl} depends on non-standard axioms {bad}"
      return false

def main (args : List String) : IO UInt32 := do
  match args with
  | modStr :: specs@(_ :: _) =>
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := modStr.toName }] {} (trustLevel := 0)
    let mut ok := true
    for s in specs do
      ok := (← checkOne env s) && ok
    return if ok then 0 else 1
  | _ =>
    IO.eprintln "usage: axcheck <Module> <decl>[:<ExpectedTypeConst>] ..."
    return 2
