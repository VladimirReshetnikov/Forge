# Source ledger

Access date: September 14, 2026. Bibliography keys below match the LaTeX article.
These are primary documentation, source repositories, research papers, or
conference/author pages. They establish the baseline and prior art; experimental
claims in the article come from the included code and `results/`, not these sites.

## Baseline and inspected integration boundary

- **grind** — https://lean-lang.org/doc/reference/latest/The--grind--tactic/
  Current documented shared-state architecture, congruence closure, constraint
  propagation, E-matching, theory solvers, and Lean proof production.
- **release434** — https://lean-lang.org/doc/reference/latest/releases/v4.34.0/
  Dated release baseline. In particular, shared-state `grind => bv_decide` and
  conditional `Sym.simp` guard discharge are existing capabilities, not Forge additions.
- **grindlia** — https://lean-lang.org/doc/reference/latest/The--grind--tactic/Linear-Integer-Arithmetic/
  Linear integer arithmetic and model-based theory combination. The latter is
  not claimed as a new Forge algorithm or confused with general MBQI.
- **grindematch** — https://lean-lang.org/doc/reference/latest/The--grind--tactic/E___matching/
  Existing E-matching behavior and term-trigger interactions.
- **grindsource** — https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Meta/Tactic/Grind/Main.lean
  Pinned source file inspected through the GitHub interface. `Params.extraFacts`,
  `assertExtra`, `GrindM.run`, and `mkGoalCore` inform the integration discussion.
  The proposed persistent `GrindAdapter` interface is not a released Lean API.

## Existing Lean components

- **aesop** — https://github.com/leanprover-community/aesop
  Structured proof search and indexed rules.
- **linarith** — https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linarith/Frontend.html
- **positivity** — https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Positivity/Basic.html
- **lincomb** — https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/LinearCombination.html
  Existing Mathlib proof reconstruction and arithmetic infrastructure.
- **sos** — https://github.com/leanprover/sos/blob/main/README.md
  Existing proof-producing nonlinear arithmetic backend and certificate architecture.
  The prototype's dictionary LP is not represented as a replacement for this project.
- **duper** — https://github.com/leanprover-community/duper
  Lean proof-producing automated reasoning.
- **leanauto** — https://arxiv.org/abs/2505.14929
  Yicheng Qian, Joshua Clune, Clark Barrett, Jeremy Avigad:
  *Lean-auto: An Interface Between Lean 4 and Automated Theorem Provers* (2025).
  Project: https://github.com/leanprover-community/lean-auto
- **leansmt** — https://github.com/ufmg-smite/lean-smt
  Supported theory boundary and reconstruction behavior, including remaining
  subgoals for unsupported proof steps. Associated paper:
  https://arxiv.org/abs/2505.15796
- **leanegg** — https://github.com/marcusrossel/lean-egg
  Historical implementation. Its discontinuation notice is a reason not to pick
  it as a new foundational dependency.

## Algorithms, prior art, and mathematical tools

- **cclemma** — https://icfp24.sigplan.org/details/icfp-2024-papers/29/CCLemma-E-Graph-Guided-Lemma-Discovery-for-Inductive-Equational-Proofs
  Cole Kurashige et al., *CCLemma: E-Graph Guided Lemma Discovery for Inductive
  Equational Proofs*, PACMPL 8 (ICFP), article 264 (2024), DOI 10.1145/3674653.
  Prior art for e-graph-guided inductive lemma discovery. The proposal does not
  claim to invent that general technique.
- **egg** — https://arxiv.org/abs/2004.03082
  Max Willsey et al., *egg: Fast and Extensible Equality Saturation* (2021).
- **z3quant** — https://microsoft.github.io/z3guide/docs/logic/Quantifiers/
  Patterns, matching loops, and model-based quantifier instantiation.
- **canonical** — https://arxiv.org/abs/2504.06239
  Chase Norman, Jeremy Avigad, *Canonical for Automated Theorem Proving in Lean* (2025).
- **canonicalmin** — https://arxiv.org/abs/2603.01463
  Chase Norman, Jeremy Avigad, *Implementing Dependent Type Theory Inhabitation
  and Unification* (2026). Typed inhabitation/unification and DTTBench context.
- **scipylp** — https://docs.scipy.org/doc/scipy/reference/generated/scipy.optimize.linprog.html
  LP interface documentation. The live documentation can differ from the
  executed SciPy **1.17.0**, which is recorded in `results/results.json`.
- **mosek** — https://docs.mosek.com/modeling-cookbook/linear.html
  Polyhedral linear optimization, Farkas-style certificates, and duality.

## Version and compatibility limits

Only the selected Lean core source was explicitly pinned to `v4.34.0` during
inspection. Other live documentation and repository README pages are dated
observations, not a tested lockfile. This archive does not assert that the newest
Mathlib, SOS, Duper, and Lean-SMT revisions build together on release day.
Select mutually compatible revisions and record a real Lake manifest during
implementation. No external project source trees or font files are vendored.

The article derives its recurrence, affine-certificate, and Bernstein identities
explicitly. Its correctness arguments are for the stated mathematical formats;
they are not claims that the Python implementation has a machine-checked
soundness proof.
