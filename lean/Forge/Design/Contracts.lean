/-
  Merged from proposal p6-proof-logging-cdcl, file lean/Contracts.lean.

  The logical/soundness contract: CertificateSpec with an explicit `sound`
  field, Proven, CheckedOutcome, FactHandle. Core Lean only.
  Complements Runtime.lean rather than duplicating it.

  NOT COMPILED as part of this file's original proposal, and not compiled
  here either unless it appears in results/lean-core-elaboration.json.
  See docs/LEAN-STATUS.md for what has and has not been checked.
-/

/-
Uncompiled design specimen. These declarations specify only a small logical
certificate contract. They do NOT provide the proposed tactic or checkers.
-/
import Lean

namespace ForgeContracts

/-- The central mathematical contract; reification needs a separate sound bridge. -/
structure CertificateSpec (Problem Certificate : Type) where
  denotes : Problem → Prop
  check : Problem → Certificate → Bool
  sound : ∀ (p : Problem) (c : Certificate), check p c = true → denotes p

/-- A real proof, not merely a solver's assertion that something was proved. -/
structure Proven where
  proposition : Prop
  proof : proposition

/-- This logical outcome does not encode the complete runtime scope mechanism. -/
inductive CheckedOutcome (target : Prop) where
  | closed (proof : target)
  | derived (facts : Array Proven)
  | unknown (reason : String)

/-- Proposed runtime handles. The publication boundary must validate Expr types,
    assumption closure, and scope; this raw record alone enforces none of them. -/
structure FactHandle where
  proposition : Lean.Expr
  proof : Lean.Expr
  scopeId : Nat
  assumptionIds : Array Nat
  environmentVersion : Nat
  metavariableVersion : Nat
  origin : Lean.Name

end ForgeContracts
