/-
  Forge: the part that needs core Lean only.

  Two proposed design contracts, one set of Mathlib-free structural proofs, the
  induction principles the closure workers lower to, and --- new, and the only
  part of this repository that closes the loop the project is named for --- a
  CHECKED certificate checker with the prototype's own certificates run through
  it.

  `Forge.Checker` is not a design sketch. `Cone.Cert.check` is a total function
  returning `Bool`; `Cone.Cert.sound` proves that when it returns `true` the
  polynomial really is nonnegative on the constrained set, for every assignment
  rather than any tested one. `Checker.Corpus` is generated from the Python
  prototype's certificate bundle and the Lean kernel checks each one by
  reduction. Every theorem in the three files depends on `propext` and
  `Quot.sound` and nothing else.

  Still true, and worth keeping in view: elaboration is not an axiom audit, and
  no `forge` TACTIC exists. What exists is a checker, its soundness proof, and
  three certificates that pass it.
-/
import Forge.Design.Runtime
import Forge.Design.Contracts
import Forge.Examples.Structural
import Forge.Closure.Principles
import Forge.Closure.Covers
import Forge.Closure.Indexing
import Forge.Checker.Poly
import Forge.Checker.Cone
import Forge.Checker.Corpus
import Forge.Checker.Bench
import Forge.Checker.Reify
import Forge.Checker.Tactic
import Forge.Checker.TacticTest
import Forge.Checker.Oracle
import Forge.Checker.Affine
import Forge.Checker.AffineCorpus
import Forge.Checker.Farkas
import Forge.Checker.Recurrence
import Forge.Checker.RecurrenceCorpus
