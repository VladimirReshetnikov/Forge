# Integration delta

Reuse ForgeContracts.CertificateSpec and the existing ForgeDesign candidate,
conditional-candidate, scope, and failure types. No alternate scheduler or proof
publication authority is proposed.

The counter worker first needs a Lean Boolean checker with a proved soundness
theorem for the caller-supplied model. A source safety bridge needs initial
coverage, source-step simulation, and source-bad implies model-bad. Negative
model traces become source refutations only after a source-lifting proof.

The equality worker needs a typed interpreter, evaluation equivariance, anchored
joint-pattern completeness, fresh-input coverage, and a positive receipt theorem.
A source one-step simulation must preserve both outputs and next-state relations.
For BEq-based code, equality lawfulness is an explicit obligation.

The mixed checker must enumerate rules from the original model and reconstruct
all representative transitions. Do not trust a producer-generated quotient edge
table. Retain original rule/input labels for negative witness lifting.

Recommended acceptance order:

1. Compile a counter receipt theorem and a source-level axes example for all
   parameters. Record actual axiom inventories.
2. Compile guarded counter reflection and the parameterized mutex controls.
3. Compile equality-pattern proofs, the derived finite-carrier theorem, cache
   equivalence, and the three-key counterexample.
4. Compile mixed direct replay and the parameterized owner-pool theorem.
5. Evaluate against strong Lean baselines with source reflection, search,
   certificate checking, bridge construction, and recompilation measured apart.

Leant/Djex integration is an optional semantic-discharge stage after checked
candidate reconstruction and a proved summary. Do not infer all-input behavior
from finite tests or bypass lexical, type, dictionary, or universe checks.
The original Church-indexing and two-universe queries are not solved here.
