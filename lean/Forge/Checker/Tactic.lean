import Lean
import Forge.Checker.Reify
import Forge.Checker.Cone
/-
  The `forge_cone` tactic: close an ordinary integer goal with a cone
  certificate, through the PROVED bridge `eval_toPoly` rather than a generated
  `simp`/`omega` script.

  WHAT THE TACTIC PRODUCES. For a goal `0 ≤ e` it builds

      cone_denote c x tp gs fs hcheck hg hf  :  0 ≤ denote x tp

  where
  * `tp`, `gs`, `fs` are `IExpr` terms reified from the goal and hypotheses,
  * `x := Env.ofList [a₀, a₁, …]` lists the atoms,
  * `hcheck : c.check (toPoly tp) (gs.map toPoly) (fs.map toPoly) = true` is
    proved by `decide` (kernel reduction of `Cert.check`; no `native_decide`),
  * `hg : AllNonneg x gs` and `hf : AllZero x fs` are nested `And.intro`s of the
    user's hypotheses (or `Int.sub_nonneg_of_le h` / `Int.sub_eq_zero_of_eq h`
    for the two-sided forms).
  `cone_denote` is `Cert.sound` composed with `eval_toPoly`. The type
  `0 ≤ denote x tp` is identified with the user's goal by DEFINITIONAL
  unfolding (`denote`, `Env.ofList`), which `Meta.check`/`isDefEq` verify here and
  the kernel re-verifies when the declaration is added. The metaprogram is
  therefore untrusted: a reification bug can make the tactic FAIL, never make it
  prove something false.

  ATOM ORDER (certificates are expressed in it). Atom `i` is variable `i` of the
  certificate's monomials. Atoms are numbered in order of first occurrence:
  1. atoms given explicitly with `(atoms := [a, b, …])`, in that order;
  2. then the goal, scanned left to right as written (for `a ≤ b`, `a` before
     `b`; for `a ≥ b`, `a` before `b`; within `u + v`, `u` before `v`);
  3. then each hypothesis in the order of the `[h₁, h₂, …]` list, each scanned
     left to right in the same way.
  Two occurrences are the same atom when they are defeq at reducible
  transparency.

  CONSTRAINT ORDER. Inequality hypotheses become the checker's `ineqs` in list
  order, equality hypotheses its `eqs` in list order (the two kinds may be
  interleaved in the list; each keeps its relative order).

  WHAT IS RECOGNISED as structure (anything else is an atom):
  `+ - * ` and unary `-` at type `Int` with the standard core instances,
  `e ^ n` with `n` a `Nat` literal, `Int` numerals `OfNat.ofNat` and
  `Int.ofNat` of a `Nat` literal. Negative literals are `-` applied to a numeral.

  Goal forms: `0 ≤ e`, `e ≥ 0`, `a ≤ b`, `a ≥ b`.
  Hypothesis forms: `0 ≤ g`, `g ≥ 0`, `a ≤ b` (contributes `b - a`), `a ≥ b`
  (contributes `a - b`), `f = 0` (contributes `f`), `a = b` (contributes `a - b`).
-/
namespace Forge.Checker.Tactic

open Lean Meta Elab Tactic
open Forge.Checker Forge.Checker.IExpr

/-! ### Reification -/

/-- A reified expression: the value (for printing) and the `IExpr` term. -/
structure R where
  val : IExpr
  term : Expr

abbrev ReifyM := StateRefT (Array Expr) MetaM

private def intTy : Expr := mkConst ``Int
private def natTy : Expr := mkConst ``Nat

/-- A `Nat` literal: raw, or `OfNat.ofNat Nat (lit) _`. -/
def natLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .mdata _ e => natLit? e
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appFn!.appArg!, e.appFn!.appArg! with
      | ty, .lit (.natVal n) => if ty.isConstOf ``Nat then some n else none
      | _, _ => none
    else none

/-- A nonnegative `Int` numeral: `OfNat.ofNat Int (lit) _` or `Int.ofNat lit`. -/
def intNumeral? (e : Expr) : Option Nat :=
  match e with
  | .mdata _ e => intNumeral? e
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appFn!.appArg!, e.appFn!.appArg! with
      | ty, .lit (.natVal n) => if ty.isConstOf ``Int then some n else none
      | _, _ => none
    else if e.isAppOfArity ``Int.ofNat 1 then natLit? e.appArg!
    else none

def isIntZero (e : Expr) : Bool := intNumeral? e == some 0

/-- The canonical numeral `(n : Int)`, as `OfNat.ofNat Int n (instOfNat n)`. -/
def mkIntNumeral (n : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [0]) intTy (mkRawNatLit n)
    (mkApp (mkConst ``instOfNat) (mkRawNatLit n))

/-- The standard instances `denote` uses. An operation whose instance is not
defeq to these is treated as an atom. -/
private def stdHAdd : Expr := mkApp2 (mkConst ``instHAdd [0]) intTy (mkConst ``Int.instAdd)
private def stdHSub : Expr := mkApp2 (mkConst ``instHSub [0]) intTy (mkConst ``Int.instSub)
private def stdHMul : Expr := mkApp2 (mkConst ``instHMul [0]) intTy (mkConst ``Int.instMul)
private def stdNeg : Expr := mkConst ``Int.instNegInt
private def stdHPow : Expr :=
  mkApp3 (mkConst ``instHPow [0, 0]) intTy natTy
    (mkApp2 (mkConst ``instPowNat [0]) intTy (mkConst ``Int.instNatPow))

private def instOk (inst std : Expr) : MetaM Bool :=
  withReducibleAndInstances (isDefEq inst std)

def atomIndex (e : Expr) : ReifyM Nat := do
  let atoms ← get
  for h : i in [0:atoms.size] do
    if ← withReducible (isDefEq atoms[i] e) then return i
  set (atoms.push e)
  return atoms.size

def mkAtom (e : Expr) : ReifyM R := do
  let i ← atomIndex e
  return ⟨.atom i, mkApp (mkConst ``IExpr.atom) (mkNatLit i)⟩

partial def reify (e : Expr) : ReifyM R := do
  let e := e.consumeMData
  if let some n := intNumeral? e then
    return ⟨.const n, mkApp (mkConst ``IExpr.const) (mkIntNumeral n)⟩
  let args := e.getAppArgs
  let bin (ctor : Name) (mk : IExpr → IExpr → IExpr) : ReifyM R := do
    let a ← reify args[4]!
    let b ← reify args[5]!
    return ⟨mk a.val b.val, mkApp2 (mkConst ctor) a.term b.term⟩
  let int3 : Bool := args.size == 6 && args[0]!.isConstOf ``Int &&
    args[1]!.isConstOf ``Int && args[2]!.isConstOf ``Int
  if int3 && e.isAppOfArity ``HAdd.hAdd 6 then
    if ← instOk args[3]! stdHAdd then return ← bin ``IExpr.add .add
  if int3 && e.isAppOfArity ``HSub.hSub 6 then
    if ← instOk args[3]! stdHSub then return ← bin ``IExpr.sub .sub
  if int3 && e.isAppOfArity ``HMul.hMul 6 then
    if ← instOk args[3]! stdHMul then return ← bin ``IExpr.mul .mul
  if e.isAppOfArity ``Neg.neg 3 && args[0]!.isConstOf ``Int then
    if ← instOk args[1]! stdNeg then
      let a ← reify args[2]!
      return ⟨.neg a.val, mkApp (mkConst ``IExpr.neg) a.term⟩
  if e.isAppOfArity ``HPow.hPow 6 && args[0]!.isConstOf ``Int
      && args[1]!.isConstOf ``Nat && args[2]!.isConstOf ``Int then
    if ← instOk args[3]! stdHPow then
      if let some n := natLit? (← instantiateMVars args[5]!) then
        let a ← reify args[4]!
        return ⟨.pow a.val n, mkApp2 (mkConst ``IExpr.pow) a.term (mkNatLit n)⟩
  mkAtom e

/-! ### Goals and hypotheses -/

/-- The syntactic shape of an `Int` comparison, sides as written. -/
inductive Shape where
  | le (a b : Expr)   -- a ≤ b
  | ge (a b : Expr)   -- a ≥ b
  | eq (a b : Expr)   -- a = b

def shapeOf? (ty : Expr) : MetaM (Option Shape) := do
  let ty ← instantiateMVars ty
  let ty := ty.consumeMData
  let test (ty : Expr) : Option Shape :=
    if ty.isAppOfArity ``LE.le 4 && ty.getAppArgs[0]!.isConstOf ``Int then
      some (.le ty.getAppArgs[2]! ty.getAppArgs[3]!)
    else if ty.isAppOfArity ``GE.ge 4 && ty.getAppArgs[0]!.isConstOf ``Int then
      some (.ge ty.getAppArgs[2]! ty.getAppArgs[3]!)
    else if ty.isAppOfArity ``Eq 3 && ty.getAppArgs[0]!.isConstOf ``Int then
      some (.eq ty.getAppArgs[1]! ty.getAppArgs[2]!)
    else none
  match test ty with
  | some s => return some s
  | none => return test (← whnfR ty)

/-- Reify two sides in textual order; a literal-zero side is not reified. -/
def reifyPair (a b : Expr) : ReifyM (Option R × Option R) := do
  let ra ← if isIntZero a then pure none else some <$> reify a
  let rb ← if isIntZero b then pure none else some <$> reify b
  return (ra, rb)

private def zeroR : R := ⟨.const 0, mkApp (mkConst ``IExpr.const) (mkIntNumeral 0)⟩

private def subR (a b : R) : R :=
  ⟨.sub a.val b.val, mkApp2 (mkConst ``IExpr.sub) a.term b.term⟩

/-- One reified hypothesis: which list it goes to, its expression, and a proof
whose type is definitionally `0 ≤ denote x expr` (or `denote x expr = 0`). -/
structure Hyp where
  isEq : Bool
  expr : R
  proof : Expr

def reifyHyp (h : Expr) : ReifyM Hyp := do
  let ty ← inferType h
  let some s ← shapeOf? ty
    | throwError "forge_cone: hypothesis{indentExpr h}\nhas type{indentExpr ty}\n\
        which is not one of the supported forms over Int: \
        0 ≤ g, g ≥ 0, a ≤ b, a ≥ b, f = 0, a = b"
  match s with
  | .le a b =>
    match ← reifyPair a b with
    | (none, some rb) => return ⟨false, rb, h⟩
    | (none, none) => return ⟨false, zeroR, h⟩
    | (some ra, rb) =>
      let rb := rb.getD zeroR
      return ⟨false, subR rb ra, mkApp3 (mkConst ``Int.sub_nonneg_of_le) b a h⟩
  | .ge a b =>
    match ← reifyPair a b with
    | (some ra, none) => return ⟨false, ra, h⟩
    | (none, none) => return ⟨false, zeroR, h⟩
    | (ra, some rb) =>
      let ra := ra.getD zeroR
      return ⟨false, subR ra rb, mkApp3 (mkConst ``Int.sub_nonneg_of_le) a b h⟩
  | .eq a b =>
    match ← reifyPair a b with
    | (some ra, none) => return ⟨true, ra, h⟩
    | (none, none) => return ⟨true, zeroR, h⟩
    | (ra, some rb) =>
      let ra := ra.getD zeroR
      return ⟨true, subR ra rb, mkApp3 (mkConst ``Int.sub_eq_zero_of_eq) a b h⟩

/-- The reified goal: `nonneg t` for `0 ≤ e` / `e ≥ 0` (target `e`), or
`le ta tb` for a goal definitionally `denote ta ≤ denote tb` (target `tb - ta`). -/
inductive GoalR where
  | nonneg (t : R)
  | le (ta tb : R)

def reifyGoal (ty : Expr) : ReifyM GoalR := do
  let some s ← shapeOf? ty
    | throwError "forge_cone: goal{indentExpr ty}\nis not of a supported form over Int: \
        0 ≤ e, e ≥ 0, a ≤ b, a ≥ b"
  match s with
  | .le a b =>
    match ← reifyPair a b with
    | (none, some rb) => return .nonneg rb
    | (none, none) => return .nonneg zeroR
    | (some ra, rb) => return .le ra (rb.getD zeroR)
  | .ge a b =>
    match ← reifyPair a b with
    | (some ra, none) => return .nonneg ra
    | (none, none) => return .nonneg zeroR
    | (ra, some rb) => return .le rb (ra.getD zeroR)
  | .eq _ _ =>
    throwError "forge_cone: goal{indentExpr ty}\nis an equation; only inequalities \
      0 ≤ e, e ≥ 0, a ≤ b, a ≥ b are supported"

/-- Everything reified from one invocation. -/
structure Problem where
  atoms : Array Expr
  goal : GoalR
  ineqs : Array Hyp
  eqs : Array Hyp

def reifyProblem (seed : Array Expr) (goalTy : Expr) (hyps : Array Expr) :
    MetaM Problem := do
  let act : ReifyM (GoalR × Array Hyp) := do
    for a in seed do
      let before := (← get).size
      let i ← atomIndex a
      if i < before then
        throwError "forge_cone: atom{indentExpr a}\nis listed twice in (atoms := ...)"
    let g ← reifyGoal goalTy
    let hs ← hyps.mapM reifyHyp
    return (g, hs)
  let ((g, hs), atoms) ← act.run #[]
  return ⟨atoms, g, hs.filter (!·.isEq), hs.filter (·.isEq)⟩

def Problem.targetR : Problem → R
  | ⟨_, .nonneg t, _, _⟩ => t
  | ⟨_, .le ta tb, _, _⟩ => subR tb ta

/-! ### Proof construction -/

private def iexprTy : Expr := mkConst ``IExpr

def envExpr (atoms : Array Expr) : Expr :=
  mkApp (mkConst ``Env.ofList) (atoms.foldr (fun a l => mkApp3 (mkConst ``List.cons [0]) intTy a l)
    (mkApp (mkConst ``List.nil [0]) intTy))

def iexprList (rs : Array R) : Expr :=
  rs.foldr (fun r l => mkApp3 (mkConst ``List.cons [0]) iexprTy r.term l)
    (mkApp (mkConst ``List.nil [0]) iexprTy)

/-- `And.intro p₁ (And.intro p₂ … True.intro)` against `AllNonneg x ts` or
`AllZero x ts`; each component's expected type is stated explicitly so that
`Meta.check` and the kernel compare it with the hypothesis by defeq. -/
def conjProof (allName : Name) (entry : Expr → Expr) (x : Expr) (hs : Array Hyp) : Expr :=
  Id.run do
    let mut acc : Expr := mkConst ``True.intro
    let mut rest : List R := []
    for h in hs.reverse do
      let restTy := mkApp2 (mkConst allName) x (iexprList rest.toArray)
      let headTy := entry (mkApp2 (mkConst ``IExpr.denote) x h.expr.term)
      acc := mkApp4 (mkConst ``And.intro) headTy restTy h.proof acc
      rest := h.expr :: rest
    return acc

private def intLe (a b : Expr) : Expr :=
  mkApp4 (mkConst ``LE.le [0]) intTy (mkConst ``Int.instLEInt) a b

private def intEq (a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) intTy a b

def elabHyps (hs : Array Term) : TacticM (Array Expr) :=
  hs.mapM fun h => do
    let e ← Term.withoutErrToSorry <| elabTerm h none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

def elabAtoms (as : Array Term) : TacticM (Array Expr) :=
  as.mapM fun a => do
    let e ← Term.withoutErrToSorry <| elabTerm a (some intTy)
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

def runForgeCone (seed : Array Expr) (hyps : Array Expr) (certStx : Term) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let goalTy ← instantiateMVars (← goal.getType)
    let cert ← Term.withoutErrToSorry <| elabTerm certStx (some (mkConst ``Cert))
    Term.synthesizeSyntheticMVarsNoPostponing
    let cert ← instantiateMVars cert
    if cert.hasMVar then
      throwError "forge_cone: the certificate{indentExpr cert}\ncontains metavariables"
    let prob ← reifyProblem seed goalTy hyps
    let x := envExpr prob.atoms
    let tp := prob.targetR
    let gs := iexprList (prob.ineqs.map (·.expr))
    let fs := iexprList (prob.eqs.map (·.expr))
    let mapToPoly (l : Expr) : Expr :=
      mkApp4 (mkConst ``List.map [0, 0]) iexprTy (mkConst ``Poly) (mkConst ``IExpr.toPoly) l
    let checkProp := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp4 (mkConst ``Cert.check) cert (mkApp (mkConst ``IExpr.toPoly) tp.term)
        (mapToPoly gs) (mapToPoly fs))
      (mkConst ``Bool.true)
    -- The certificate check, by kernel-checkable `decide`.
    let hcheckMVar ← mkFreshExprSyntheticOpaqueMVar checkProp
    try
      let rest ← Tactic.run hcheckMVar.mvarId! (evalTactic (← `(tactic| decide)))
      unless rest.isEmpty do throwError "decide left goals"
    catch ex =>
      throwError "forge_cone: certificate REJECTED. `Cert.check` did not evaluate to \
        `true` on the reified problem (target, {prob.ineqs.size} inequality and \
        {prob.eqs.size} equality constraint(s), atoms {prob.atoms.toList}).\n\
        Check that the certificate is for this goal, in this atom order and this \
        hypothesis order.\nUnderlying error: {ex.toMessageData}"
    let hcheck ← instantiateMVars hcheckMVar
    let hg := conjProof ``AllNonneg (intLe (mkIntNumeral 0)) x prob.ineqs
    let hf := conjProof ``AllZero (fun d => intEq d (mkIntNumeral 0)) x prob.eqs
    let proof := match prob.goal with
      | .nonneg t =>
        mkAppN (mkConst ``cone_denote) #[cert, x, t.term, gs, fs, hcheck, hg, hf]
      | .le ta tb =>
        mkAppN (mkConst ``cone_denote_le) #[cert, x, ta.term, tb.term, gs, fs, hcheck, hg, hf]
    -- Type-check the whole term (this compares each hypothesis with its
    -- `denote` form by defeq), then compare its type with the goal.
    try
      Meta.check proof
    catch ex =>
      throwError "forge_cone: internal proof term does not type-check (a hypothesis \
        is not definitionally its reified form): {ex.toMessageData}"
    let proofTy ← inferType proof
    unless ← isDefEq proofTy goalTy do
      throwError "forge_cone: the reified statement{indentExpr proofTy}\nis not \
        definitionally the goal{indentExpr goalTy}"
    goal.assign proof
    replaceMainGoal []

syntax atomsClause := "(" &"atoms" " := " "[" term,* "]" ")"

/-- `forge_cone [(atoms := [a₀, …])] [h₁, …] using c` closes an integer
inequality goal with the cone certificate `c`. See the module docstring for the
atom order and the accepted shapes. -/
syntax (name := forgeCone) "forge_cone" (ppSpace atomsClause)? (ppSpace "[" term,* "]")?
  " using " term : tactic

elab_rules : tactic
  | `(tactic| forge_cone $[(atoms := [$as,*])]? $[[$hs,*]]? using $c) => do
    let seed ← elabAtoms ((as.map (·.getElems)).getD #[])
    let hyps ← elabHyps ((hs.map (·.getElems)).getD #[])
    runForgeCone seed hyps c

/-! ### Printing the reified problem as JSON -/

/-- Collected, zero-free, padded to `n` variables: the shape
`tools/export_lean_cone.py` reads, `{"n": k, "terms": [[[e₀,…], "c"], …]}`. -/
def polyJson (n : Nat) (p : Poly) : Json :=
  let p := (collect p).filter (fun t => t.2 != 0)
  let pad (m : Mono) : List Nat := m ++ List.replicate (n - m.length) 0
  Json.mkObj [
    ("n", toJson n),
    ("terms", Json.arr (p.map (fun t =>
      Json.arr #[toJson (pad t.1), Json.str (toString t.2)])).toArray)]

def problemJson (prob : Problem) : MetaM Json := do
  let n := prob.atoms.size
  let atoms ← prob.atoms.mapM fun a => return Json.str (toString (← ppExpr a))
  return Json.mkObj [
    ("atoms", Json.arr atoms),
    ("p", polyJson n (toPoly prob.targetR.val)),
    ("inequalities", Json.arr (prob.ineqs.map (fun h => polyJson n (toPoly h.expr.val)))),
    ("equalities", Json.arr (prob.eqs.map (fun h => polyJson n (toPoly h.expr.val))))]

/-- `forge_reify [(atoms := …)] [h₁, …]` prints the reified goal and hypotheses
as JSON, in the atom order `forge_cone` would use. It does not change the goal. -/
syntax (name := forgeReify) "forge_reify" (ppSpace atomsClause)? (ppSpace "[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| forge_reify $[(atoms := [$as,*])]? $[[$hs,*]]?) => do
    let goal ← getMainGoal
    goal.withContext do
      let seed ← elabAtoms ((as.map (·.getElems)).getD #[])
      let hyps ← elabHyps ((hs.map (·.getElems)).getD #[])
      let prob ← reifyProblem seed (← instantiateMVars (← goal.getType)) hyps
      logInfo m!"{(← problemJson prob).compress}"

end Forge.Checker.Tactic
