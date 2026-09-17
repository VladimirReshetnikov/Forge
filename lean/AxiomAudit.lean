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

  EXEMPTIONS are explicit, reasoned, and must be NECESSARY. A theorem listed in
  `exemptions` may additionally use the axioms named for it; if it no longer uses
  them, the audit FAILS, so a stale exemption cannot quietly widen the policy.
  Currently one: `compose_with_grind` tests that `forge_cone` facts compose with
  the stock `grind` tactic, and `grind`'s own proofs use `Classical.choice`. That
  axiom enters through Lean's tactic, not through anything in Forge's proof path,
  and the same composition via `omega` (`compose_with_omega`) needs no exemption.

  `Forge/Checker/OracleTest.lean` is not imported here because it needs `python`
  on PATH. Its theorems pass the same audit when it is added to the imports;
  that was checked when this file was written (612 theorems at the time).
-/
open Lean Elab Command

elab "#audit_forge_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound]
  -- (theorem, extra axioms it may use, why). Each must be NECESSARY.
  let exemptions : List (Name × List Name × String) := [
    (`Forge.Checker.TacticTest.compose_with_grind, [``Classical.choice],
      "stock `grind` uses Classical.choice; compose_with_omega shows the same composition without it")]
  let mut exemptUsed : List Name := []
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
    let extra := match exemptions.find? (·.1 == n) with
      | some (_, ex, _) => ex
      | none => []
    unless axs.all (fun a => allowed.contains a || extra.contains a) do bad := bad.push (n, axs)
    if !extra.isEmpty && axs.any (extra.contains ·) then exemptUsed := n :: exemptUsed
  if total == 0 then
    throwError "axiom audit: found no theorems under Forge.Checker -- the audit would be vacuous"
  for (n, _, why) in exemptions do
    unless exemptUsed.contains n do
      throwError m!"axiom audit FAILED: exemption for {n} is not necessary (the theorem is missing or no longer uses the exempted axioms), so it must be removed: {why}"
  unless bad.isEmpty do
    let lines := bad.toList.map fun (n, axs) => m!"\n  {n} depends on {axs}"
    throwError m!"axiom audit FAILED: {bad.size} of {total} theorem(s) use axioms outside \
      [propext, Quot.sound]:{MessageData.joinSep lines m!""}"
  logInfo m!"axiom audit passed: {total} theorems under Forge.Checker, all within [propext, Quot.sound] except {exemptions.length} documented, necessary exemption(s)"
  for (n, ex, why) in exemptions do
    logInfo m!"  exempt: {n} may also use {ex} -- {why}"
  for (k, v) in buckets do
    logInfo m!"  {v} with {k}"

#audit_forge_axioms
