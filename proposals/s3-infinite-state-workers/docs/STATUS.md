# Evidence and boundaries

## Executed

Three standard-library Python producers, independent certificate replay, 27
unit-test methods, 640 generated differential cases, ten named examples, and
1,300 invalid-certificate mutation checks. `results/summary.json` records the
original experiment environment and single-run timings. `reproduction-check.json`
records a subsequent rerun with the delivered checker and exact comparison of
corpus objects; it is not another 640 distinct cases.

Positive receipts and negative witnesses are different objects. Unknown is not
accepted by a checker. Debug statistics are not evidence. The caller supplies
the original model; a certificate never selects its own model.

The oracles use complete concrete exploration only on generated models whose
state space is finite by token conservation and/or the proved name-carrier
cutoff. They reuse the checker interpreter. The independent replay process does
not import any producer or oracle module.

The 1,300 mutations are mostly schema or mandatory-content tests. Targeted
semantic regression tests are in `tests/test_core.py`. Positive tests also accept
valid redundant bases and noncanonical atom labels.

## Mathematical arguments, not machine-checked proofs

The article proves the scalar predecessor identity, affine-family separation,
backward-receipt soundness and saturation completeness, fresh-input coverage,
orbit equivalence soundness and finite-carrier cutoff, and exact mixed-model
transport for the stated languages.

## Not executed or not delivered

No Lean/elan executable is present in the authoring runtime. A search for a
suitable compiler integration did not find one. `lean/CounterLemmas.lean` is
**NOT_RUN**; its `#print axioms` commands have no claimed output. It has no
placeholder proofs, but that alone says nothing about whether it compiles.

There is no Lean certificate checker, source reifier, installed `forge` tactic,
Leant/Djex integration, or head-to-head tactic benchmark in this delivery.
Existing baseline Forge elaborations are not results of these new workers.

## Fragment boundaries

Counter safety: fixed finite dimension, finite control, natural consume/produce
vectors, upward-closed targets, independent nonnegative affine initial families.
No inhibitor arcs, zero tests, arbitrary reachability, fairness, or liveness.

Equality equivalence: deterministic first-matching total rules, fixed finite
register count, equality/copy language, anchored constants, Boolean or optional
atom outputs, one output per input. No key order/hash/arithmetic, unbounded
storage, arbitrary callbacks, or internal name-allocation semantics.

Mixed safety: nondeterministic equality rules plus fixed natural counter updates.
Bad guards cannot read an unspecified input. Initial families share one anchored
register/control state. No unbounded per-name counter map.

## Input robustness

The CLI validates schemas and rejects several malformed forms, but this remains
a research implementation, not a hostile-input service. Text-byte and guard-depth
limits do not bound every allocation, integer bit length, certificate length,
or CPU cost. Run resource-sensitive workloads with process-level limits.
