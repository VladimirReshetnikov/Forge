# Forge analytic extensions

Start with **article/forge_analytic_extensions.pdf**. Editable source is beside it.

Three repository-relative additions to the audited Forge design:

1. Anchored rational remainder certificates for elementary analytic expressions.
2. Exact integrating-factor ladder search for global exponential-polynomial inequalities.
3. Rational-series upper barriers, harmonic divergence certificates, and least-index Cauchy witnesses.

These are executable research prototypes, **not an implemented Lean tactic**.
The source-to-Lean bridge and checker soundness have not been compiled or verified
in Lean. A passing Python checker is not a Lean-kernel proof.

## Reproduce

Tested with Python 3.13.5. Core search and replay use the standard library only.
From this directory:

```sh
python -m unittest discover -s tests -v
python -S tools/verify.py
python tools/experiments.py --output reproduced-results
python tools/modulus_checks.py --output reproduced-moduli.json
```

The experiment runner requires a new output directory. It cannot silently replace
the recorded run. It writes a failure receipt if an assertion fails.

Optional independent diagnostics (SymPy 1.14.0, mpmath 1.3.0):

```sh
python -m pip install -r requirements-testing.txt
python tools/oracle_checks.py --output reproduced-oracle.json
```

The checker import guard in `tools/verify.py` prevents search and optional numerical
libraries from being imported during replay. `-S` also disables site packages.
Neither this separation nor the diagnostics constitute formal verification.

## Recorded evidence

| Unit | Result |
| --- | --- |
| Certificate records | 246 accepted; 230 distinct source/domain subjects |
| Anchored records | 62 accepted; 61 distinct subjects |
| Same-model, factor-erasing ablation | 8 accepted records / subjects |
| Ladder records | 43 accepted; 42 distinct subjects |
| Upper-barrier records | 81 accepted; 67 distinct series |
| Harmonic-minorant records | 60 accepted; 60 distinct series |
| Specified certificate mutations | 738 rejected |
| Standard-library unit-test methods | 25 passed |
| Taylor-polynomial symbolic checks | 62 passed |
| Sampled remainder diagnostics | 620 passed; samples are not proofs |
| Differential-identity symbolic checks | 68 passed |
| Shifted-tail symbolic checks | 141 passed |
| Least-index witness checks | 324 passed; 115 improve the coarse index |

There are two repeated elementary source subjects across named subfamilies.
Seven optimized series are each requested at three cutoffs. These overlaps are
explicit in `results/duplicate-audit.json`. Counts must not be advertised as 246
distinct solved Lean goals, and unit tests, mutations, samples, and certificates
must not be summed into a single success total.

## Package map

- `article/`: LaTeX article and rendered PDF.
- `prototype/forge_analytic/algebra.py`: dense exact arithmetic for search.
- `prototype/forge_analytic/jets.py`: anchored model construction and search.
- `prototype/forge_analytic/ladders.py`: exact differential search and planted-case generator.
- `prototype/forge_analytic/tails.py`: constructive tail classification, constant optimization, and moduli.
- `prototype/forge_analytic/checker.py`: independent sparse replay, external-subject binding, bounded strict decoding.
- `tests/test_core.py`: standard-library tests and controls.
- `tools/`: reproduction, isolated replay, optional diagnostics, PDF build.
- `results/`: exact recorded problems/certificates, measurements, mutations, diagnostics, source audit.
- `lean/SemanticBridges.lean`: two uncompiled candidate bridge lemmas; not a certificate checker.
- `STATUS.md`: precise implementation and validation boundaries.

For direct imports, set `PYTHONPATH=prototype`; command-line tools set their own
module path. Search functions return candidate data. Always pass the expected
subject externally to `checker.verify`, and never treat its result as Lean evidence.

## Build the article

```sh
sh tools/build_pdf.sh
```

Requires pdfLaTeX with common stock packages. No shell escape, external bibliography
processor, or redistributed fonts are needed.

## Source scope

Forge was audited at `c98e47c5f804e92880fc1d0e378c1b95832b685c`.
The audit covered specified merged sections and supporting documentation; it was
not an exhaustive line-by-line review of all eighteen frozen original proposals.
The article explicitly credits existing Taylor-model, verified-numerics, and
comparison methods, including LeanCert. No claim of priority over that literature
or performance advantage against an existing Lean tactic is made.
