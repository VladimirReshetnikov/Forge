# Incremental contribution audit

Reviewed 2026-09-15. Repository snapshots:

- Forge: `674521027d968d59f7b83220ed52304a85cb55e2`
- Leant: `6bf05ad78c467989e68290f2d08bbed40802d485`
- Djex: `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`
- Mathlib reference pin inherited from Forge: `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`
- Lean reference baseline inherited from Forge: `leanprover/lean4:v4.34.0`

## Directly inspected source locations

Forge: README.md; docs/STATUS.md; docs/IDEAS-FROM-LEANT-DJEX.md;
article/sections/05-structural.tex (successive line ranges through 880);
article/sections/B-provenance.tex (1–300);
lean/Forge/Design/Contracts.lean; recursive main tree metadata.

Leant: README.md; docs/behavioral-synthesis.md (1–180); main commit metadata.
Djex: README.md (1–180); main branch metadata.

Mathlib at the above pin: Mathlib/Algebra/MvPolynomial/Eval.lean (1–100);
Mathlib/Data/Nat/Choose/Basic.lean (1–180); Mathlib/Data/Matrix/Mul.lean (1–80).

Connector responses for very long files were occasionally truncated. The audit
uses the contiguous structural portions, the explicit status ledger, and the
merged provenance inventory; it is not a claim of a byte-by-byte audit of all
nine archived proposals or of the neighboring repositories. The GitHub search
index returned no hits even for a known term, so its empty results were NOT used
as evidence of absence. Container cloning was unavailable (DNS resolution).

## Existing ideas not claimed as contributions

The outer proof planner, grind cooperation, dependent generalization, lemma
synthesis, finite Horn slicing, CEGIS polynomial sums, conserved quantities,
SOS/cone/ideal membership certificates, Bernstein/Sturm, arithmetic witnesses,
LJT negative evidence, scope/receipt/axiom policy, and exact source ownership.

## Deltas developed and implemented here

1. Observable row-space closure: complete fixed rational finite-alphabet
   linear fragment; coefficient matrices as certificates; concrete words.
2. Target-generated pullback ideal closure: construct auxiliary generators
   automatically; arbitrary polynomial multiplier certificates; polynomial
   initial parameterizations; no jointly unknown invariant/multiplier system.
3. Pole-free binomial-sum recurrence synthesis: exact linear nullspace search
   modulo a primitive cross-multiplied binomial relation; endpoint-safe
   certificate templates; explicit separation of recurrence from uniqueness.

The new library APIs, certificates, worked examples, executable Python corpus,
mutation tests, and the universal-behavior adapter design are the incremental
contribution. The underlying linear-algebra, ideal-theoretic, and summation
methods have antecedents cited in the article; no claim of new mathematical
priority is made.
