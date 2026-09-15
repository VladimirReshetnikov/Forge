# FORGE — Beyond `grind` through structural search and certified algebra

**Start with [`article/forge.pdf`](article/forge.pdf).** This package contains a detailed design article, executable exact-arithmetic prototypes, tests, stored certificates, raw experimental results, and candidate Lean replay scripts.

## Status and scope

The full `forge` tactic is **a design, not an implemented Lean tactic**. Six algorithmic components are implemented in Python. The final run passed **275 pytest test instances**. All **198 constructed benchmark cases** produced certificates, and all 198 stored certificates passed a separate recheck using only the Python standard library.

**No Lean executable was available in the authoring environment. The Lean files have not been compiled. There is no measured comparison against `grind`, Aesop, `nlinarith`, or any other Lean tactic.** The included mechanism ablations are restricted versions of our own Python algorithms, not theorem-prover baselines. The examples are constructed, often from known certificates, and are not a held-out mathematical corpus.

The article distinguishes mathematical soundness arguments, tested Python checking, generated Lean candidate source, and the proposed production implementation. A Python check is not a Lean-kernel proof.

## Contents

- `article/forge.tex`, `article/sections/`, `article/forge.pdf`: editable LaTeX sources and the rendered article.
- `prototype/forge/`: sparse rational polynomials, exact certificate checking, search algorithms, recurrence synthesis, affine witnesses, and univariate Sturm certificates.
- `prototype/tests/`: unit, mutation, independent symbolic, and expected-Unknown tests.
- `prototype/run_experiments.py`: deterministic generation and timing of the 198 cases.
- `prototype/verify_certificates.py`: bounded JSON decoding and standard-library-only exact rechecking.
- `prototype/emit_lean.py`: generates candidate proof scripts, without executing Lean.
- `lean/`: a pinned Lean/Mathlib candidate replay project, plus an optional local build recorder.
- `results/`: actual test log, per-instance CSV/JSON, all certificates, summary, and execution status.

## Implemented fragments

| Component | Search mechanism | Certificate acceptance |
|---|---|---|
| Global rational quadratics | Exact Schur-complement PSD decomposition | Expand weighted squares and compare exactly |
| Finite polynomial cones | Floating HiGHS LP support proposal; rational repair | Nonnegative exact weights and polynomial identity |
| Multivariate boxes | Exact Bernstein coefficients and dyadic subdivision | Recompute all leaf bounds and check full coverage |
| Univariate intervals with zeros | Rational factorization; square-factor/Sturm reduction | Exact factor identity, Sturm chain, root count, endpoint signs |
| Polynomial additive recurrences | Increasing polynomial ansatz and rational coefficient matching | Universal base and finite-difference identities |
| Affine witnesses | Rational RREF for `A W = B`, `A d = c` | Exact matrix identities; optional integral coefficients |

The integer witness mode is incomplete. The finite-cone oracle is not a general SOS/SDP solver. The Bernstein worker may fail at exact zeros. The univariate checker has resource/degree caps. `None` means **Unknown**, not a proved counterexample.

## Reproduce the Python results

Python 3.13.5 was used. Numerical/test dependencies are pinned to their actually executed versions.

```sh
python -m venv .venv
# Activate .venv using the command appropriate to your shell.
python -m pip install -r prototype/requirements.txt
cd prototype
python -m pytest -q
python run_experiments.py
python -S verify_certificates.py
python emit_lean.py
```

`run_experiments.py` performs three searches per case and overwrites the measurement files with new timings. Warm-up/import time is not part of the per-case measurements. Search time includes any checking performed internally by that search routine; the explicit recheck column is a separate run. Timing numbers are specific to this environment and small constructed cases.

The `python -S` command avoids site packages. Rechecking does not call SciPy, NumPy, or SymPy. The decoder applies modest size and format checks, but is research tooling rather than a hardened service for hostile uploads.

## Candidate Lean proofs — uncompiled here

The project pins:

- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`.

The toolchain file at that exact Mathlib commit was inspected and matches the Lean version. The candidate project contains a quadratic proof, seven power-sum proofs, an affine witness, an explicit 32-leaf Bernstein proof, accumulator induction, a cross-theory equality, and a factored sign proof. **There is no generic Lean Sturm checker, no complete induction planner, and no implemented `forge` tactic in these files.**

In a suitable Lean environment:

```sh
cd lean
lake update
lake build
# Optional: record the local build result without modifying original status:
python run_checks.py
```

Mathlib dependencies and compiled artifacts must be available or built. These commands were not executed in the authoring environment. `run_checks.py` records build success/failure, not a full axiom-whitelist audit. Some declarations print their axiom dependencies as a starting point for inspection. No admitted theorem bodies or oracle axioms are intentionally inserted in the candidate source.

## Rebuild the article

From the `article` directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error forge.tex
```

The main source uses the files in `sections/`; keep the source directory structure intact. A standard TeX Live installation with the packages declared in the preamble is sufficient. No external bibliography program or proprietary fonts are required.

## Research findings to interpret carefully

Current `grind` already supports substantial algebra, arithmetic, extensionality, function-valued congruence, model-based theory combination, and library suggestions. Those are baseline features, not claimed FORGE innovations. The proposal adds structural planning, construction, and new certificate-producing workers around that core.

The article also distinguishes native-code trust from a kernel-only policy. A certificate-producing external solver is not automatically kernel-only if its checker is executed through a trusted native-result mechanism.

The most concrete complementary result is the zero-aware univariate method: a finite dyadic Bernstein-only cover cannot certify a nonzero polynomial whose zero remains in a leaf interior. Square-factor/Sturm certificates avoid this obstruction. This is a statement about the specified mechanisms, not a measured failure of Lean's existing automation.
