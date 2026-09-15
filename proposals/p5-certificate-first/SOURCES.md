# Sources and provenance

Inspected September 14, 2026 (America/Los_Angeles). These establish baseline
behavior, available APIs, library roles, and related work. Prototype findings
come from the code and results in this package, not from these sources.

## Baseline and pinned source

- Lean reference, grind: https://lean-lang.org/doc/reference/latest/The--grind--tactic/
- Lean grind API: https://leanprover-community.github.io/mathlib4_docs/Lean/Meta/Tactic/Grind/Types.html
- Action source, inspected at v4.34.0: https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Meta/Tactic/Grind/Action.lean
- Release metadata, v4.34.0: https://github.com/leanprover/lean4/releases/tag/v4.34.0
- Mathlib pinned revision: https://github.com/leanprover-community/mathlib4/tree/1cf325a0cf67aca2b04d76b5380ff6a9e410aefa
- Tactic reference and trust distinctions: https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/

The Lean release, source file, mathlib toolchain and mathlib revision were read
through the GitHub connector. The release was published September 14, 2026.
The mathlib commit timestamp is September 15 in UTC (September 14 locally).
No successful Lean build is implied by these metadata reads.

## Existing tools and research

- Aesop: https://github.com/leanprover-community/aesop
- Duper: https://github.com/leanprover-community/duper
- Lean-SMT paper: https://arxiv.org/html/2505.15796v1
- Lean-SMT implementation: https://github.com/ufmg-smite/lean-smt
- Learned Interventions Inside Lean 4's grind: https://arxiv.org/html/2607.22972v1
- Mathlib linarith/nlinarith: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linarith/Frontend.html
- Mathlib ring: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Ring/Basic.html
- Mathlib positivity: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Positivity/Basic.html
- SciPy linprog: https://docs.scipy.org/doc/scipy/reference/generated/scipy.optimize.linprog.html

No claim is made that all optional integrations are compatible with the pinned
Lean release. Compatibility and proof-rule tests are explicit future gates.
No external paper or third-party repository archive is redistributed.

## Our execution evidence

- results/pytest.txt: 73 passing pytest items in the recorded run.
- results/benchmarks.json and CSV files: exact synthetic configurations and
  single-run measurements. This is not a Lean benchmark.
- results/cone_certificates.json: nine named successful cone certificates.
- results/invariant_certificates.json: 49 invariant certificates.
- results/certificate_validation.txt: independent reload validation of all 58.
- results/lean_export.txt: source generation, not compilation.
- results/lean_comparisons.json: explicitly NOT RUN, Lake absent.

The article's mathematical derivations explain certificate sufficiency.
Executable Python checking is not presented as mechanized Lean verification.
