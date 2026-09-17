import Lean
import Forge.Checker.Oracle
/-
  `forge` — THE GATE 1 FRONTEND, FIRST MILESTONE.

  Gate 1 of the design (article §17) is "trustworthy orchestration": a frontend,
  a deterministic compatibility mode, full state rollback, worker contracts,
  replay records, and an axiom-policy audit. Its exit criteria: a restricted mode
  reproduces a pinned baseline suite without new axioms; a malformed proof or an
  admitted theorem is rejected; a failed branch provably cannot leak into its
  sibling. "Only existing proof-producing leaf tactics need run at this stage."

  WHAT THIS IS. A tactic `forge` that tries a FIXED, ordered list of workers on
  the main goal:

      decide      (core)
      omega       (core)
      forge_cone? (Forge, via the oracle; OFF in restricted mode)
      grind       (core)

  For each worker it
    - saves the full tactic state and runs the worker;
    - on ANY failure, including runtime limits, restores that state, so nothing
      the worker assigned, introduced or logged survives into the next attempt;
    - on apparent success, does NOT take the worker's word for it: it
      instantiates the proof term itself and rejects it if it contains `sorry`,
      if it uses a free variable outside the goal's context, if it does not
      type-check against the ORIGINAL goal, or if any constant it uses depends
      on an axiom outside the policy
      (propext, Quot.sound, and -- unless `forge.allowChoice` is false --
      Classical.choice, which stock `grind` needs);
    - accepts the first proof that passes, and emits a replay record: which
      worker closed the goal, a `Try this:` suggestion with that worker's
      script, and the outcome of every attempt before it.

  WHAT THIS IS NOT. It is not the planner. It does not decompose goals, choose
  workers by goal shape, share facts between workers, or run anything in
  parallel. It is the orchestration layer's skeleton, built so that its three
  exit criteria can be tested -- see `FrontendTest.lean`.

  TRUST. The frontend adds nothing to what the kernel checks: an accepted proof
  is exactly the term the worker produced, checked like any other. What the
  frontend adds is REFUSAL -- of `sorry`, of disallowed axioms, and of state left
  behind by failures.
-/
namespace Forge.Frontend

open Lean Meta Elab Tactic
open Forge.Checker.Tactic (shapeOf?)

register_option forge.restricted : Bool := {
  defValue := false
  descr := "forge: run only existing Lean leaf tactics (decide, omega, grind); never call the oracle"
}

register_option forge.allowChoice : Bool := {
  defValue := true
  descr := "forge: accept proofs depending on Classical.choice (stock grind uses it)"
}

register_option forge.maxOracleHyps : Nat := {
  defValue := 8
  descr := "forge: the most local hypotheses passed to forge_cone? (the oracle's own bound is 8)"
}

register_option forge.verbose : Bool := {
  defValue := false
  descr := "forge: include wall time and each rejected worker's reason in the replay record"
}

register_option forge.test.admitFirst : Bool := {
  defValue := false
  descr := "TEST ONLY: first try a worker that admits the goal; the frontend must reject it"
}

register_option forge.test.choiceFirst : Bool := {
  defValue := false
  descr := "TEST ONLY: first try a worker whose proof uses Classical.choice"
}

register_option forge.test.malformedFirst : Bool := {
  defValue := false
  descr := "TEST ONLY: first try a worker that assigns the goal an ill-typed term"
}

register_option forge.test.escapeFirst : Bool := {
  defValue := false
  descr := "TEST ONLY: first try a worker whose proof mentions a variable outside the goal's context"
}

/-- TEST ONLY. Closes the main goal by assigning `True.intro` WITHOUT a type check,
so the proof term does not prove the goal. A frontend that trusts `getUnsolvedGoals`
would accept it; the kernel would only object later, at `theorem` time. -/
elab "forge_test_malformed" : tactic => do
  let g ← getMainGoal
  g.assign (mkConst ``True.intro)
  replaceMainGoal []

/-- TEST ONLY. Closes the main goal with a local hypothesis that exists only inside
this worker: the proof term mentions a free variable the goal's context does not
have, so it proves the goal from an assumption the user never made. -/
elab "forge_test_escape" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  let h ← withLocalDeclD `phantom ty pure
  g.assign h
  replaceMainGoal []

/-- One attempt, for the replay record. -/
structure Attempt where
  worker : String
  accepted : Bool
  reason : String
  ms : Nat

/-- Axioms the policy allows. -/
def allowedAxioms (opts : Options) : List Name :=
  [``propext, ``Quot.sound] ++ (if forge.allowChoice.get opts then [``Classical.choice] else [])

/-- Every axiom, outside the policy, that some constant in `pf` depends on. -/
def disallowedAxioms (pf : Expr) : TacticM (List Name) := do
  let allowed := allowedAxioms (← getOptions)
  let mut bad : Array Name := #[]
  for c in pf.getUsedConstants do
    for a in (← collectAxioms c) do
      unless allowed.contains a || bad.contains a do
        bad := bad.push a
  return bad.toList

/-- Local hypotheses `forge_cone?` can use: Int comparisons with accessible names. -/
def oracleHyps : TacticM (Array Ident) := do
  let limit := forge.maxOracleHyps.get (← getOptions)
  let mut out : Array Ident := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.userName.hasMacroScopes then continue
    if out.size ≥ limit then break
    if (← shapeOf? d.type).isSome then
      out := out.push (mkIdent d.userName)
  return out

/-- The workers, in the fixed order that makes `forge` deterministic. -/
def workers : TacticM (Array (String × TSyntax `tactic)) := do
  let opts ← getOptions
  let mut ws : Array (String × TSyntax `tactic) := #[]
  if forge.test.admitFirst.get opts then
    ws := ws.push ("admit (test)", ← `(tactic| admit))
  if forge.test.choiceFirst.get opts then
    ws := ws.push ("choice (test)", ← `(tactic| exact Classical.byContradiction fun h => absurd trivial (by simp_all)))
  if forge.test.malformedFirst.get opts then
    ws := ws.push ("malformed (test)", ← `(tactic| forge_test_malformed))
  if forge.test.escapeFirst.get opts then
    ws := ws.push ("escape (test)", ← `(tactic| forge_test_escape))
  ws := ws.push ("decide", ← `(tactic| decide))
  ws := ws.push ("omega", ← `(tactic| omega))
  unless forge.restricted.get opts do
    let hs ← oracleHyps
    ws := ws.push ("forge_cone?", ← `(tactic| forge_cone? [$hs,*]))
  ws := ws.push ("grind", ← `(tactic| grind))
  return ws

/-- Run one worker on `goal` with full rollback. Returns the rejection reason,
or `none` if the worker's proof was accepted (and the state is kept). -/
def runWorker (goal : MVarId) (stx : TSyntax `tactic) : TacticM (Option String) := do
  let saved ← saveState
  let goalType ← instantiateMVars (← goal.getType)
  let goalCtx := (← goal.getDecl).lctx
  let outcome ← tryCatchRuntimeEx
    (do
      evalTactic stx
      unless (← getUnsolvedGoals).isEmpty do
        throwError "the worker left goals open"
      let pf ← instantiateMVars (mkMVar goal)
      if pf.hasSorry then
        throwError "REJECTED: the proof is admitted, not proved"
      if pf.hasExprMVar then
        throwError "REJECTED: the proof still contains metavariables"
      -- The proof may use only the goal's own hypotheses: a free variable from
      -- anywhere else is an assumption the user never made.
      let escaped := (collectFVars {} pf).fvarIds.filter (!goalCtx.contains ·)
      unless escaped.isEmpty do
        throwError "REJECTED: the proof uses {escaped.size} variable(s) outside the goal's context"
      -- The proof must be well typed AND prove the original statement. Checked
      -- in the goal's own context, so nothing the worker introduced is in scope.
      let wellTyped ← withLCtx goalCtx (← goal.getDecl).localInstances do
        try
          Meta.check pf
          isDefEq (← inferType pf) goalType
        catch _ => pure false
      unless wellTyped do
        throwError "REJECTED: the proof term does not have the goal's type"
      let bad ← disallowedAxioms pf
      unless bad.isEmpty do
        throwError m!"REJECTED: the proof depends on axioms outside the policy: {bad}"
      pure none)
    (fun ex => do return some (← ex.toMessageData.toString))
  if outcome.isSome then
    -- Restore EVERYTHING: metavariable assignments, local context, the goal list,
    -- and the messages the failed worker logged. A failed branch leaves nothing.
    saved.restore (restoreInfo := true)
  return outcome

syntax (name := forge) "forge" : tactic

elab_rules : tactic
  | `(tactic| forge) => do
    let ref ← getRef
    let goal ← getMainGoal
    let mut log : Array Attempt := #[]
    for (name, stx) in ← workers do
      let t0 ← IO.monoMsNow
      let r ← runWorker goal stx
      let ms := (← IO.monoMsNow) - t0
      match r with
      | none =>
        log := log.push ⟨name, true, "", ms⟩
        -- The default record is DETERMINISTIC -- worker names only -- so a
        -- baseline suite can pin it. Times and reasons vary between runs and
        -- machines, and are shown only with `forge.verbose`.
        let rejected := log.pop.toList.map (·.worker)
        if forge.verbose.get (← getOptions) then
          let detail := log.pop.toList.map fun a => s!"{a.worker} ({a.ms} ms): {a.reason.take 120}"
          logInfo m!"forge: closed by {name} in {ms} ms; rejected before it: {detail}"
        else if rejected.isEmpty then
          logInfo m!"forge: closed by {name}"
        else
          logInfo m!"forge: closed by {name}; rejected before it: {rejected}"
        Meta.Tactic.TryThis.addSuggestion ref stx (origSpan? := ref)
        return
      | some why =>
        log := log.push ⟨name, false, (String.join ((why.splitOn "\n").intersperse " ")), ms⟩
    let table := log.toList.map fun a => m!"\n  {a.worker} ({a.ms} ms): {a.reason.take 160}"
    throwError m!"forge: no worker closed the goal{MessageData.joinSep table m!""}"

end Forge.Frontend
