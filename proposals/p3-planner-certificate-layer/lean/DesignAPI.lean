/- Proposed data-contract sketch, NOT COMPILED or wired into grind.
   A candidate is deliberately not called a checked proof. No claim that a
   structure with an Expr field enforces soundness: the acceptance boundary
   described in the article must validate it in its exact environment. -/
import Lean

namespace ForgeDesign
open Lean

structure Limits where
  maxHeartbeats : Nat := 200000
  maxCandidates : Nat := 256
  maxProofNodes : Nat := 1000000
  maxCertificateBytes : Nat := 16000000
  deriving Inhabited

inductive TrustPolicy where
  | standardAxioms
  | explicitNativeEvaluation
  deriving Inhabited, Repr

structure ScopeKey where
  environmentRevision : String
  contextRevision : Nat
  localAssumptions : Array FVarId

structure Obligation where
  id : Nat
  scope : ScopeKey
  goal : MVarId
  expectedType : Expr
  depth : Nat

structure Candidate where
  obligationId : Nat
  origin : ScopeKey
  term : Expr
  -- Diagnostics only: actual transitive dependencies must be recomputed.
  reportedDependencies : Array Name := #[]

structure ConditionalCandidate where
  obligationId : Nat
  premises : Array Obligation
  -- Must elaborate as a proof constructor from ALL premises to the goal.
  constructorTerm : Expr

inductive FailureKind where
  | unsupported
  | budgetExhausted
  | cancelled
  | staleScope
  | rejectedEvidence
  deriving Inhabited, Repr

inductive EngineReply where
  | candidate (p : Candidate)
  | conditional (p : ConditionalCandidate)
  | progress (newCandidates : Array Candidate)
  | noResult (reason : FailureKind) (diagnostic : String)

-- Implementation must provide submit/replay in a trusted acceptance wrapper.
-- There is intentionally no executable 'forge' tactic in this sketch.

end ForgeDesign
