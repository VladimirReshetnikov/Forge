/-
  Forge: the part that needs core Lean only.

  Two proposed design contracts and one set of Mathlib-free structural proofs.
  This is the only library here with recorded compilation evidence: all three
  files elaborate against leanprover/lean4:v4.34.0. See
  results/lean-core-elaboration.json.
-/
import Forge.Design.Runtime
import Forge.Design.Contracts
import Forge.Examples.Structural
