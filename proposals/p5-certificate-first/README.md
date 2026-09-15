# Forge: a certificate-first design beyond Lean's grind

**Design report and executable Python research prototypes, not a released Lean
tactic.** The article is in `article/forge.tex` and `article/forge.pdf`.

## What was actually executed

Python exact-certificate prototypes implement demand-directed Horn search,
sparse nonlinear cone discovery, Bernstein box subdivision, and polynomial
recurrence-invariant discovery. The recorded run has **73 passing pytest cases**,
**109 accepted nonlinear certificates** (9 named + 100 generated), **43/45 box
certificates**, and **49/49 recurrence invariants**. All 24 deliberately false
polynomials returned `unknown` with no accepted certificate. Nine named cone
certificates and all 49 invariant certificates are exported as JSON and
revalidated separately. Search and validators are separated; the polynomial
representation is shared and differential-tested against SymPy.

These are bounded, deliberately synthetic experiments. The Horn comparison is
against our own forward-chaining implementation, **not against Lean's grind**.
Python checkers are not formally verified and do not replace Lean's kernel.

## Reproduce

Python 3.11+ is the intended minimum; the exact tested versions are recorded in
`results/benchmarks.json`. A virtual environment is recommended.

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r prototype/requirements.txt
bash scripts/reproduce.sh
```

Alternatively, run `python -m pip install -e prototype` and install pytest.
The `requirements.txt` bounds are compatibility suggestions, not a promise that
every later dependency version is tested. A tested-version snapshot is supplied
as `prototype/requirements-tested.txt`.

## Contents

- `article/`: comprehensive LaTeX article and PDF, numerical tables, bibliography.
- `prototype/forge/`: exact polynomial arithmetic, discovery and validators.
- `prototype/tests/`: positive, negative, adversarial and differential tests.
- `prototype/run_benchmarks.py`: fixed-seed synthetic experiments.
- `prototype/validate_artifacts.py`: separately reload and validate saved JSON.
- `prototype/export_lean.py`: emit explicit mathlib replay proofs.
- `results/`: raw JSON/CSV data, validation logs, and explicit Lean NOT RUN status.
- `lean/`: pinned project and generated proof source, **not compiled here**.
- `scripts/`: reproduction, optional Lean smoke comparison, and article build.
- `SOURCES.md`: source locations and provenance; no third-party source archives.

## Limits worth testing first

A degree-2 cone cannot certify the degree-4 box product. The bounded square
basis cannot certify the tested Motzkin polynomial. Bernstein subdivision does
not finish on `(x-1/3)^2` under the tested depth cap, despite nonnegativity.
The demand prover is a one-sort, head-covering Horn toy; it is not a dependent
Lean elaborator, E-matcher, or complete general first-order prover.

The supplied Lean code is a replay target, not an executed result. There was no
Lean/Lake executable and no successful installation route in this environment.
No claimed speedup, solved-goal gain, or kernel validation against actual Lean is
included. Production integration and its acceptance gates are specified in the
article.

## Article sources

`article/forge.tex` is the modular source. `article/forge-standalone.tex` includes
all chapters, tables and references in one file for convenient separate use.
Build the modular article with `bash scripts/build_article.sh`; regenerate the
standalone source with `python scripts/assemble_article.py` after editing.
