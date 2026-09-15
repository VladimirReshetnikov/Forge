/-
  Forge: the part that needs core Lean only.

  Two proposed design contracts, one set of Mathlib-free structural proofs, and
  the induction principles the closure workers lower to. This is the library
  with recorded compilation evidence: all six files elaborate against
  leanprover/lean4:v4.34.0. See results/lean-core-elaboration.json and
  results/lean-closure-elaboration.json.

  Elaboration is not an axiom audit and does not make any of these an
  implemented tactic. No `forge` tactic exists.
-/
import Forge.Design.Runtime
import Forge.Design.Contracts
import Forge.Examples.Structural
import Forge.Closure.Principles
import Forge.Closure.Covers
import Forge.Closure.Indexing
