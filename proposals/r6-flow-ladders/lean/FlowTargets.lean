/-!
Acceptance-target propositions for a future Forge Flow implementation.

These are DEFINITIONS OF PROPOSITIONS, not theorems or proofs.
No Flow tactic/checker is implemented here. This file was not compiled in the
creation environment. It contains no sorry and introduces no axioms, but that
alone does not constitute proof or compilation evidence.
-/
import Mathlib

namespace ForgeFlowTargets

-- Four cofactor steps: 1, 1, 1, 2.
def symmetric : Prop :=
  ∀ x : ℝ, 0 ≤ x →
    0 ≤ Real.exp (2 * x) - (2 + x ^ 2) * Real.exp x + 1

-- Two cofactor steps: 1, 1; terminal polynomial x.
def rationalEnvelopeResidual : Prop :=
  ∀ x : ℝ, 0 ≤ x → 0 ≤ (x - 2) * Real.exp x + x + 2

-- The denominator guard belongs to the source bridge.
def rationalEnvelope : Prop :=
  ∀ x : ℝ, 0 ≤ x → x < 2 → Real.exp x ≤ (x + 2) / (2 - x)

def hyperbolicCusaResidual : Prop :=
  ∀ x : ℝ, 0 ≤ x →
    0 ≤ x * (Real.cosh x + 2) - 3 * Real.sinh x

def hyperbolicWilkerResidual : Prop :=
  ∀ x : ℝ, 0 ≤ x →
    0 ≤ (Real.sinh x) ^ 2 * Real.cosh x + x * Real.sinh x
      - 2 * x ^ 2 * Real.cosh x

def hyperbolicLazarevicResidual : Prop :=
  ∀ x : ℝ, 0 ≤ x →
    0 ≤ (Real.sinh x) ^ 3 - x ^ 3 * Real.cosh x

-- Interval-restricted uniqueness: a real root, not a rational approximation.
def lambertBracket : Prop :=
  ∃! x : ℝ, x ∈ Set.Icc (1 / 2 : ℝ) (3 / 5 : ℝ) ∧
    x * Real.exp x = 1

def twoSeparateBrackets : Prop :=
  (∃! x : ℝ, x ∈ Set.Icc (1 / 2 : ℝ) 1 ∧ Real.exp x = 3 * x) ∧
  (∃! x : ℝ, x ∈ Set.Icc (3 / 2 : ℝ) 2 ∧ Real.exp x = 3 * x)

-- True but outside the specified scalar ladder grammar. Route to algebra.
def squareControl : Prop :=
  ∀ x : ℝ, 0 ≤ x → 0 ≤ (Real.exp x - 2) ^ 2

-- A false universal statement; the intended goal is its negation.
def falseTangentRefutation : Prop :=
  ¬ (∀ x : ℝ, 0 ≤ x → 1 + 2 * x ≤ Real.exp x)

end ForgeFlowTargets
