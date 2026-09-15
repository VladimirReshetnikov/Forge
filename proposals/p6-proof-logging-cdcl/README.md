# Forge: Beyond grind

Technical design and tested algorithm prototypes, prepared 14 September 2026.

Start with **article/forge.pdf**. The complete editable source is
**article/forge.tex** (bibliography included). The design targets a cooperating
Lean tactic built around native `grind`, not a replacement of its existing core.

## Artifact status

| Artifact | Status |
| --- | --- |
| Proof-logging CDCL + integer difference logic | Implemented and tested in Python |
| Sparse rational polynomial cone checker | Implemented and tested in Python |
| Restricted dictionary-SOS / constraint-product LP search | Implemented and tested; not a full SDP or nonlinear decision procedure |
| Polynomial accumulator-invariant CEGIS | Implemented and tested for the stated recurrence family |
| Search-independent replay of saved certificates | Tested with `python -S`, standard library only |
| Integrated Forge Lean tactic and plugins | Proposed; not implemented |
| `lean/Examples.lean` and `lean/Contracts.lean` | Uncompiled integration specimens |
| Comparison against an executed Lean `grind` | Not performed; Lean was unavailable |

No claim of measured superiority over `grind` is made. The performance baseline
in this bundle is its own chronological DPLL implementation. The padded-core
benchmarks are deliberately artificial diagnostics, not realistic speed claims.

## Reproduce discovery and tests

Tested interpreter: Python 3.13.5. From this directory:

```sh
python -m pip install -r requirements.txt
python prototype/run_tests.py --out reproduced-results
python -S prototype/replay_certificates.py --results reproduced-results
```

To control numerical-library threading on Linux/macOS:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python prototype/run_tests.py --out reproduced-results
```

On PowerShell, the corresponding optional settings are:

```powershell
$env:OPENBLAS_NUM_THREADS = '1'
$env:OMP_NUM_THREADS = '1'
python prototype/run_tests.py --out reproduced-results
```

The fixed main seed is 20260914. Use a separate output directory to preserve the
recorded results. Timing will vary across runs, Python versions, and machines.

## Replay the supplied certificates without any installed search libraries

```sh
python -S prototype/replay_certificates.py --results results
```

Expected counts: 8 SAT/theory logs, 8 polynomial certificates (7 discovered +
1 manually supplied), 6 induction certificates, 12 rejected induction mutations,
and 3 skipped unknown polynomial search results. The script fails on missing
certificate families rather than accepting an empty directory.

The SAT checker separately replays RUP additions and validates integer difference
lemmas by exact coefficient summation. The polynomial checker compares exact
rational coefficient maps. The induction checker uses sparse rational polynomial
substitution, not the SymPy implementation used by the synthesis oracle.
These are Python checks, not Lean kernel checks or formally verified Python.

## Main recorded results

* 1,000 random CNF and 500 random CNF/integer-difference cases matched exhaustive
  reference results: 1,278 SAT and 222 UNSAT. Every UNSAT certificate replayed;
  all 222 truncated certificates were rejected. Additional edge and mutation
  tests are reported in `results/summary.json`.
* 7 of 10 small polynomial search cases certified. The remaining results are
  unknown, including the deliberate dictionary gap `(2*x+y)^2 >= 0`.
* 100 planted rational-square checker tests were independently cross-checked
  using SymPy. These were not 100 additional oracle search successes.
* 6 polynomial invariants were synthesized for the generalized accumulator
  recurrence, then checked by exact base/step identities and independent replay.

## File layout

- `article/forge.tex`, `article/forge.pdf`: comprehensive design, proofs,
  experiments, integration plan, limitations, and 25 cited references.
- `prototype/cdcl_idl.py`: CDCL(T), proof logging, RUP replay, difference-logic
  checker, exhaustive theory oracle, and chronological DPLL baseline.
- `prototype/polynomial.py`: exact sparse arithmetic/checker and an untrusted
  SciPy/HiGHS search oracle with rational reconstruction.
- `prototype/induction.py`: exact counterexample-guided bivariate polynomial
  invariant synthesis for the explicitly described recurrence family.
- `prototype/run_tests.py`: deterministic tests and benchmark/certificate output.
- `prototype/replay_certificates.py`: standard-library-only saved replay.
- `results/`: machine-readable evidence, logs, certificates, and timings.
- `lean/`: uncompiled logical contracts and theorem specimens; not Forge.
- `requirements.txt`, `Makefile`: reproduction conveniences.

## Build the PDF

From `article/`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error forge.tex
```

A TeX Live installation with `newtx`, `tcolorbox`, `listings`, `hyperref`, and
standard mathematical packages is sufficient. No shell escape, fonts copied
from the machine, or separate bibliography tool is required.

## Integration cautions

The source review identified Lean v4.34.0 as the latest release on the preparation
date. This is not a tested compatible manifest for Mathlib, SOS, LP, or the
other suggested libraries. Pin a mutually compatible dependency set before
compiling the Lean specimens. No `lakefile` pretending to be tested is supplied.

Strict kernel-only proof replay and compiled/native checker replay are distinct
trust profiles. The article explains why a certificate-based tactic cannot simply
be assumed to satisfy the strict profile without auditing its proof dependencies.

The original prototype code is supplied under MIT-0; external projects are only
referenced, not redistributed, and retain their own licenses.
