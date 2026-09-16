# Lean integration status and implementation contract

Status: DESIGN ONLY. No `.lean` file in this package is represented as tested.
No Lean executable was available; no comparison with grind or other tactics ran.

Suggested namespace: Forge.Resources. Suggested proposed modules (not existing APIs):
Basic / Summary / Frontier / Parameters / Reify / Tactic.

1. Basic: `Marking d := Fin d -> Nat`, Transition.consume/produce; Step requires
   consume <= marking before natural subtraction. Prove frame monotonicity and
   `pre(b)=consume+(b-produce)` (truncated Nat subtraction) exactly.
2. Summary: compressed programs with empty/step/seq/repeat; demand and signed
   effect semantics; prove domain and endpoint theorems by structural induction.
   Preserve primitive-step count separately; endpoint equality ignores it.
3. Frontier: a Boolean finite checker whose correctness theorem needs only
   target inclusion, backward closure, and positive run for each basis element.
   It does NOT need a verified saturation algorithm or a formal Dickson proof.
4. Parameters: scalar minimal threshold and finite-cap clipping theorem for
   nonnegative affine maps; checked finite Pareto coverage.
5. Reify: begin with exact finite-place multisets. Use Mathlib's
   Multiset.count_add, count_sub and le_iff_count. A guard on multiset subtraction
   is mandatory; natural subtraction is not integer subtraction.
6. Tactic: external JSON is an untrusted candidate. Construct the object problem
   from the actual elaborated Lean goal, prove/check the semantic bridge, then
   apply check_sound to the exact certificate. Reuse Forge's existing authority
   and environment discipline rather than inventing a parallel verifier.

Mathlib rolling documentation was inspected, not compiled at Forge's pin.
Pin and check imports/names in CI before treating this list as an integration.

Acceptance: a source-level theorem quantified over ALL initial populations,
replayed in a fresh Lean process with recorded axiom inventory; a genuinely
false source property rejected; guard, transition-order, source-query and
parameter-binding mutations rejected. An object-level vector identity alone
must not be reported as proof of a multiset or source-program theorem.
