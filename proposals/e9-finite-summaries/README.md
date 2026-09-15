# Forge: Certified Finite Summaries for Infinite Proofs

Research increment prepared on 2026-09-15 for Vladimir Reshetnikov.

Start with **article/forge_finite_summaries.pdf**. The complete LaTeX source is
beside it; the main file inputs `sections/` and `references.tex`.

## Contributions

1. Rational word-equivalence search with finite matrix closure certificates or
   concrete separating words; polynomial input alphabets and an affine-state,
   polynomial-observation lift.
2. Exact bounded telescoping for sums of `q^k binom(n,k)^p`, with a shifted-support
   flux and separately checked interior and exceptional boundary identities.
3. Polynomial Ore common-left-multiple certificates and complete natural-root
   covers that determine the extra seeds needed for recurrence equality.

The underlying mathematical algorithms are established methods. The article
explains the specific increment over the audited Forge design and a proposed
Leant/Djex consumer; it does not claim global priority.

## Actual status

The authoritative run is `results/run-4/`: 245 accepted entries, 245 rejected
specified invalidating mutations, 100 differential word-model tests, and two
insufficient-ansatz outcomes reported as UNKNOWN. A separate replay passes with
site packages disabled and SymPy absent. All 41 unit tests pass.

**These are exact Python checks, not Lean-kernel proofs.** No integrated tactic,
Lean source reifier, or head-to-head Lean benchmark is delivered. The core
semantic lemma in `lean/WordSimulation.lean` is clearly marked UNCOMPILED.
A singularity/seed plan does not prove that two sequences obey a recurrence or
that the required seed values agree. See `docs/STATUS.md` for acceptance gates.

## Reproduce

Producer tested with Python 3.13.5 and SymPy 1.14.0. The code uses Python 3.10+
syntax; other interpreter versions were not tested. Install the producer
requirement into an appropriate environment:

```sh
python -m pip install -r prototype/requirements.txt
python -S prototype/replay.py results/run-4/certificates.json
(cd prototype && python -m unittest discover -s tests -v)
python prototype/run_experiments.py --out results/reproduction
python prototype/check_parametric_square.py
```

The experiment output directory must be new or empty. The replay path uses only
Python's standard library. It does not import SymPy, Gaussian elimination, or
any producer module. It shares the small exact representation/arithmetic module
with producer serialization; it is not a formally verified independent prover.

Build the article using a standard TeX installation:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error forge_finite_summaries.tex
```

## Layout

- `prototype/forge_summaries/`: exact representations, search-free checkers,
  reachable-space search, monomial lift, telescoping search, and Ore search.
- `prototype/run_experiments.py`: deterministic corpus; seed 681437.
- `prototype/replay.py`: strict JSON loading and search-independent replay.
- `prototype/tests/`: 41 unit and regression tests.
- `results/run-4/`: authoritative certificate inputs, per-run metrics, mutations,
  and summary. Run 2 remains as historical evidence, not pooled acceptance.
- `results/RUN_HISTORY.md`: failures, repairs, and scope of measurements.
- `results/parametric-square.json`: supplementary universal-weight polynomial
  check; not part of the 245-entry corpus and not a Lean proof.
- `docs/`: non-duplication audit and status ledger.
- `lean/`: uncompiled generic semantic proof candidate, not a matrix checker.

The original GitHub repositories were not modified. No external library source,
third-party executable, checksum file, or font file is included.
