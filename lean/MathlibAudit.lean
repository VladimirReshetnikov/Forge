import Forge.Generated.Bernstein
import Forge.Generated.Induction
import Forge.Generated.Invariants
import Forge.Generated.SOS
import Forge.Generated.SOSExtra
import Forge.Generated.Witnesses
import Forge.Examples.Accumulator
import Forge.Examples.Arithmetic
import Forge.Examples.Basic
import Forge.Examples.CrossTheory
import Forge.Examples.Lattice
import Forge.Examples.Mixed
import Forge.Examples.Residue
import Forge.Real.Cone
import Forge.Real.Examples
/-
  AXIOM AUDIT for the Mathlib-dependent files: every theorem DECLARED in one of
  the modules imported above -- found by walking the environment and asking
  which module each constant came from, not by a list of names -- must depend on
  nothing beyond `propext`, `Classical.choice` and `Quot.sound`.

  `Classical.choice` is allowed here, unlike in `AxiomAudit.lean`, because
  Mathlib's reals and its `ring`/`norm_num`/`linarith` proofs are built on it.
  What this audit catches is everything else: `sorryAx`, `Lean.ofReduceBool`
  (`native_decide`), and any `axiom` a file declares.

  Like `AxiomAudit.lean`, it FAILS TO COMPILE on a violation, and fails if it
  finds no theorems at all. Compiled by `tools/build_mathlib_forge.py`.
-/
open Lean Elab Command

elab "#audit_mathlib_forge_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : List Name := [`Forge.Generated, `Forge.Examples, `Forge.Real]
  let mut perModule : Std.HashMap Name Nat := {}
  let mut bad : Array (Name × Name × List Name) := #[]
  for (n, ci) in env.constants.toList do
    let isThm := match ci with
      | .thmInfo _ => true
      | _ => false
    unless isThm do continue
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless prefixes.any (·.isPrefixOf mod) do continue
    perModule := perModule.insert mod (perModule.getD mod 0 + 1)
    let axs := (← liftCoreM (collectAxioms n)).toList
    unless axs.all allowed.contains do bad := bad.push (mod, n, axs)
  let total := perModule.fold (fun acc _ v => acc + v) 0
  if total == 0 then
    throwError "mathlib axiom audit: found no theorems -- the audit would be vacuous"
  unless bad.isEmpty do
    let lines := bad.toList.map fun (m, n, axs) => m!"\n  {m}: {n} depends on {axs}"
    throwError m!"mathlib axiom audit FAILED: {bad.size} of {total} theorem(s) use axioms \
      outside [propext, Classical.choice, Quot.sound]:{MessageData.joinSep lines m!""}"
  logInfo m!"mathlib axiom audit passed: {total} theorems in {perModule.size} modules, all within [propext, Classical.choice, Quot.sound]"
  let rows := perModule.toList.mergeSort (fun a b => a.1.toString < b.1.toString)
  for (m, k) in rows do
    logInfo m!"  {k} in {m}"

#audit_mathlib_forge_axioms
