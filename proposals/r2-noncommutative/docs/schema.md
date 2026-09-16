# Exact schema and interpretation contract

`ncforge.problem.v1` has exactly these fields:
`schema`, `kind`, `atoms`, `involution`, `target`, `relations`, `positives`.
`kind` is `equality`, `operator`, or `trace`. Atoms are zero-based integer IDs.
The involution must have the correct length and square to the identity.

A polynomial is a lexicographically sorted list of `[word,numerator,denominator]`.
Words are lists of valid atom IDs. The empty word denotes one. Coefficients are
nonzero reduced rational numbers with positive denominators. Duplicate words
and explicit zero terms are rejected. Rational scalar fields in certificates
are `[numerator,denominator]`; they may be zero in canonical form `[0,1]`.
Python booleans and floats are not accepted as integer encodings.

`ncforge.certificate.v1` is separate from the original problem:

- `equality`: `schema`, `kind`, `ideal`.
- `operator`: `schema`, `kind`, `ideal`, `squares`.
- `trace`: `schema`, `kind`, `ideal`, `squares`, `commutators`.
- `matrix_countermodel`: `schema`, `kind`, `dimension`, `matrices`, `vector`.

An ideal term has `relation`, `left`, `right`, `weight`; it means
`weight * left * original_relation[relation] * right`.
A square term has `weight`, `positive`, `q`; the weight is nonnegative.
`positive=-1` means the unit; other indices refer to the original positive
premises. It means `weight * star(q) * premise * q`.
A commutator term has `weight`, `left`, `right` and denotes
`weight * (left*right - right*left)`.
Matrix entries and witness-vector entries are canonical rational pairs.

The checker expands all receipt contributions and compares them to the ORIGINAL
target. It never accepts a claim that a remainder, solver answer, or Gram matrix
is correct without replay. Matrix countermodels check each WHOLE relation
matrix, then a nonzero target-vector product.

Equality means a universal conditional identity over all associative unital
Q-algebras. Its schema permits no positivity constraints. Matrix witnesses
refute only this universal interpretation. Equality-schema involutions do not
impose self-adjointness on countermodel matrices.

Operator/trace mean real square matrices of arbitrary finite dimension satisfying
the original transpose involution, all relations, and all PSD premises.
The target and PSD premises must be syntactically self-adjoint. Operator receipts
prove PSD; trace receipts prove nonnegative trace. Trace commutators cannot be
included in an operator receipt. Unknown fields are rejected, including unsupported
fixed dimensions or changed coefficient fields.

Current checker limits: 12 atoms, word length 24 in serialized words, 10,000 terms
per bounded general list, 200 relations or positive premises, 8,192-bit integer
inputs, matrix dimension 100, and 2,000,000 metered product operations. The meter
counts polynomial term pairs or cubic dense matrix multiplication operations.
These are research guardrails, not a hardened hostile-input guarantee. JSON
size/depth and intermediate coefficient growth need additional production limits.

A Python `accepted` result is not a Lean proof. Exact source reification and
kernel-checked interpretation must be implemented separately.
