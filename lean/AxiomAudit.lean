import ForgeCore
/-
  AXIOM AUDIT: every theorem under `Forge.Checker`, enumerated from the
  environment, must depend on nothing beyond `propext` and `Quot.sound`.

  This file FAILS TO COMPILE if any theorem leaks another axiom -- `sorryAx`,
  `Lean.ofReduceBool` (what `native_decide` introduces), `Classical.choice`, or
  anything a generated file declares. The compiler's exit code is the verdict,
  not a line of output someone has to read: this repository has twice been misled
  by output lines, once by a `sorry` scan that matched a comment and once by a
  file that failed with ten errors while printing `does not depend on any axioms`.

  WHY ENUMERATE. An earlier audit printed axioms for a fixed list of theorem
  names. Adversarial review showed a generated corpus could declare a theorem the
  list did not name -- proving `1 = 2` from an injected `axiom` -- and the list's
  output stayed clean. Walking the environment has no such blind spot.

  RUN:  cd lean && LEAN_PATH=.lake/build/lib lean AxiomAudit.lean

  `Forge/Checker/OracleTest.lean` is not imported here because it needs `python`
  on PATH. Its theorems pass the same audit when it is added to the imports;
  that was checked when this file was written (612 theorems at the time).
-/
open Lean Elab Command

elab "#audit_forge_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound]
  let mut total : Nat := 0
  let mut bad : Array (Name × List Name) := #[]
  let mut buckets : Array (List Name × Nat) := #[]
  for (n, ci) in env.constants.toList do
    unless (`Forge.Checker).isPrefixOf n do continue
    let isThm := match ci with
      | .thmInfo _ => true
      | _ => false
    unless isThm do continue
    if n.isInternal then continue
    total := total + 1
    let axs := (← liftCoreM (collectAxioms n)).toList
    let key := axs.mergeSort (fun a b => a.toString < b.toString)
    match buckets.findIdx? (·.1 == key) with
    | some i => buckets := buckets.modify i (fun kv => (kv.1, kv.2 + 1))
    | none => buckets := buckets.push (key, 1)
    unless axs.all (allowed.contains ·) do bad := bad.push (n, axs)
  if total == 0 then
    throwError "axiom audit: found no theorems under Forge.Checker -- the audit would be vacuous"
  unless bad.isEmpty do
    let lines := bad.toList.map fun (n, axs) => m!"\n  {n} depends on {axs}"
    throwError m!"axiom audit FAILED: {bad.size} of {total} theorem(s) use axioms outside \
      [propext, Quot.sound]:{MessageData.joinSep lines m!""}"
  logInfo m!"axiom audit passed: {total} theorems under Forge.Checker, all within \
    [propext, Quot.sound]"
  for (k, v) in buckets do
    logInfo m!"  {v} with {k}"

#audit_forge_axioms
