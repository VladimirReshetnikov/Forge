# Lean integration specification — NOT IMPLEMENTED / NOT COMPILED

No Lean compiler was available during this work. This directory intentionally
contains no `.lean` file that could be mistaken for a working tactic or checker.
The article's Section 8 gives source-level obligations and exact existing API
names inspected in the official Mathlib reference.

## First vertical slice

Prove the finite matrix pairing identity and the soundness of the adjoint
non-homotopy checker. Reconstruct the exact source theorem asserting
`Not (Nonempty (Homotopy F G))` for the integral p=2,t=1 fixture. The positive
t=2 fixture must also replay. A source-domain switch to Q must invalidate the
negative integral claim. Record the compiled theorem and its axiom inventory.

## Proposed modules (these do not yet exist)

- `Forge/IntegralComplex/MatrixData.lean`: finite matrix and degree syntax.
- `Forge/IntegralComplex/MatrixCheck.lean`: reflected exact arithmetic semantics.
- `Forge/IntegralComplex/Coordinates.lean`: whole-kernel and quotient theorems.
- `Forge/IntegralComplex/Reduction.lean`: f/g/h soundness and composition.
- `Forge/IntegralComplex/HomotopyDual.lean`: pairing and modular obstruction.
- `Forge/IntegralComplex/Reify.lean`: original-source/basis correspondence proofs.
- `Forge/IntegralComplex/MathlibAdapter.lean`: existing Homotopy/homology objects.

Use existing `Mathlib.LinearAlgebra.Matrix.ToLin` conversions and
`Mathlib.Algebra.Homology.Homotopy` structures rather than a parallel homology
foundation. The docs' `Homotopy.comm` field arranges the equation as
F = dH + Hd + G; the prototype uses F-G = dH + Hd. Composition order and
basis selections require proved translations, not textual substitutions.

## Required source ownership

Keep the exact coefficient ring, ordered bases, grading, differential expressions,
map expressions, local context, and all bridge proofs. A certificate checked
against arbitrary JSON matrices has no authority over another Lean source goal.
Numeric synthesis accepts concrete integer entries. Universal theorems for a
fixed concrete differential may leave the cycle vector quantified.

## Gates after the first slice

Whole-kernel coordinates, universal cycle filling, and induced maps with both
commuting squares; then checked reductions and reconstruction of original
homotopies. Keep the nonunit-stagnation fixture and the middle-exactness
B=(2) fixture. Do not replace an integral homotopy goal by rational existence,
induced-homology equality, or a record with unproved soundness fields.
