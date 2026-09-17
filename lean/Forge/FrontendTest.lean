import Forge.Frontend
/-
  Tests for `forge`, the Gate 1 frontend, one section per exit criterion of Gate 1
  (article §17). All run in RESTRICTED mode -- existing leaf tactics only, no
  oracle -- so this file needs no Python. The oracle path is tested in
  `Checker/OracleTest.lean`.

  Every message below is pinned with `#guard_msgs`, which is possible because
  the frontend's default replay record is deterministic.
-/
set_option forge.restricted true

namespace Forge.FrontendTest

open Lean Elab Tactic Meta

/-! ## 1. A pinned baseline suite, and the axioms it introduces

Gate 1: "the restricted mode reproduces a pinned baseline suite without
introducing new axioms". Each goal is closed by the first worker that succeeds;
the record names it and the ones rejected before it; and `#print axioms` shows
exactly what the accepted proof depends on. `grind`'s proofs use
`Classical.choice`; that is the policy's default, and section 3 shows it can be
turned off. -/

/--
info: forge: closed by omega; rejected before it: [decide]
---
info: Try this:
  [apply] omega
-/
#guard_msgs in
theorem baseline_linear (x y : Nat) (h : x < y) : x + 1 ≤ y := by forge

/--
info: forge: closed by decide
---
info: Try this:
  [apply] decide
-/
#guard_msgs in
theorem baseline_closed : (2 : Nat) + 2 = 4 := by forge

/--
info: forge: closed by grind; rejected before it: [decide, omega]
---
info: Try this:
  [apply] grind
-/
#guard_msgs in
theorem baseline_congruence (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by forge

/-- info: 'Forge.FrontendTest.baseline_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms baseline_linear

/-- info: 'Forge.FrontendTest.baseline_closed' does not depend on any axioms -/
#guard_msgs in #print axioms baseline_closed

/-- info: 'Forge.FrontendTest.baseline_congruence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms baseline_congruence

/-! ## 2. An admitted proof is rejected

Gate 1: "a deliberately malformed proof or admitted theorem is rejected". A test
worker closes the goal with `sorry` BEFORE any real worker runs. The frontend
must refuse it -- by inspecting the proof term, not by trusting the worker --
and the accepted proof must carry no `sorryAx`. -/

/--
info: forge: closed by omega; rejected before it: [admit (test), decide]
---
info: Try this:
  [apply] omega
-/
#guard_msgs in
set_option forge.test.admitFirst true in
theorem admitted_rejected (x : Int) (h : 0 ≤ x) : 0 ≤ x + 1 := by forge

/-- info: 'Forge.FrontendTest.admitted_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms admitted_rejected

/-! ## 3. The axiom policy is enforced, in both directions

A test worker proves `True` through `Classical.byContradiction`, which depends on
`Classical.choice`. With choice DISALLOWED it is rejected and `decide` closes the
goal with no axioms at all. With choice ALLOWED (the default) the same worker is
accepted -- so the rejection above is the policy acting, not the worker failing. -/

/--
info: forge: closed by decide; rejected before it: [choice (test)]
---
info: Try this:
  [apply] decide
-/
#guard_msgs in
set_option forge.allowChoice false in
set_option forge.test.choiceFirst true in
theorem choice_rejected : True := by forge

/-- info: 'Forge.FrontendTest.choice_rejected' does not depend on any axioms -/
#guard_msgs in #print axioms choice_rejected

#guard_msgs (drop info) in
set_option forge.test.choiceFirst true in
theorem choice_accepted : True := by forge

/-- info: 'Forge.FrontendTest.choice_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms choice_accepted

/-! ## 4. A failed branch cannot leak into its sibling

Gate 1: "a failed branch provably cannot leak a local equality into its sibling".
This drives `runWorker` directly: a worker unifies the goal `?w = 5` with
`3 = 5` -- ASSIGNING `?w := 3` -- and then fails. After the frontend restores
state, the witness must be unassigned again and the goal list exactly as before.
If the assignment leaked, every later worker would be handed `3 = 5`. -/

elab "check_rollback" : tactic => do
  let w ← mkFreshExprMVar (mkConst ``Nat)
  let g ← mkFreshExprMVar (← mkEq w (mkNatLit 5))
  let outer ← getGoals
  setGoals [g.mvarId!]
  let r ← Forge.Frontend.runWorker g.mvarId!
    (← `(tactic| (refine (show (3 : Nat) = 5 from ?_); fail "deliberate failure after assigning")))
  let assigned ← w.mvarId!.isAssigned
  let goals ← getGoals
  setGoals outer
  logInfo m!"rollback: rejected={r.isSome} witness_assigned_after={assigned} \
    goals_restored={goals.length == 1 && goals.head! == g.mvarId!}"

/-- info: rollback: rejected=true witness_assigned_after=false goals_restored=true -/
#guard_msgs in
example : True := by
  check_rollback
  trivial

/-! ## 5. When no worker applies, `forge` fails and says why

Restricted mode has no nonlinear worker, so AM-GM is out of reach. (A first draft
of this test gave the goal as a hypothesis so the example could close; `omega`
then proved it by treating the products as atoms, and the frontend was right to
accept. The example now closes with an honest certificate instead.) -/

example (x y : Int) : 2 * (x * y) ≤ x ^ 2 + y ^ 2 := by
  fail_if_success forge
  forge_cone using
    ({ scale := 1, squares := [{ weight := 1, powers := [], poly := [([1], 1), ([0, 1], -1)] }],
       multipliers := [] } : Forge.Checker.Cert)

end Forge.FrontendTest
