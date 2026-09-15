# Evidence and source status

Research date: 14 September 2026 (the authoring session's local date).

## Documentation/source observations

- The user supplied the moving `latest` grind manual. It and its algebra, arithmetic,
  E-matching, and case-analysis sections were read online.
- GitHub's release endpoint identified Lean **v4.34.0**, published
  **2026-09-14T14:04:36Z**. This is not the installed compiler version: no Lean compiler
  was installed in the execution environment.
- `leanprover/lean4/src/Lean/Meta/Tactic/Grind/Main.lean` was read through the GitHub
  connector on the development branch. Its returned file blob id was
  `f0355a372e08f69d863b94ee39541a8b96d300e5`; this is not a repository commit id.
- The opening portion of `Types.lean` was also fetched at tag `v4.34.0`.
  Solver-extension details were inspected in the generated current API documentation.
  None of this substitutes for compiling the proposed adapter against a pinned tag.
- LeanHammer, Aesop, Duper, Lean-auto, LeanSMT, Mathlib linarith, and Lean proof
  validation documentation were consulted as existing work, not presented as new.
- The current Reservoir entry marks the `lean-egg` frontend deprecated in favor of
  `grind`. The proposal does not recommend that deprecated frontend as its core.
- The validation reference describes per-computation native-evaluation axioms since
  Lean 4.29. The proposed strict policy cannot audit only the historical
  `Lean.trustCompiler` name.

The full reference list, including directly navigable URLs, is in `article/forge.tex`
and the PDF. No third-party paper or repository is bundled; the archive contains
original implementation and writing, experimental output, and reference metadata.

## Execution observations

Python 3.13.5, SymPy 1.14.0, SciPy 1.17.0, NumPy 2.3.5; versions and platform are
also recorded in `results/experiments.json`. Tests and saved artifact replay were
executed. Search and checking run in ordinary Python, not in Lean's kernel.

`ReplayExamples.lean` was authored but not compiled. No result for `grind`, Aesop,
LeanHammer, LeanSMT, or the proposed `forge` on the candidate Lean benchmark goals
was measured. No baseline outcome should be inferred from the Python experiment
statistics. Numerical producer failures and bounded-search failures are UNKNOWN,
not refutations of the original proposition.
