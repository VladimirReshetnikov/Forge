# FORGE: a certificate-first successor architecture for Lean's `grind`

Start with **article/forge.pdf**. The LaTeX source is **article/forge.tex**.

## Status

This archive contains a detailed tactic design and four **executed Python
algorithm prototypes**. It does **not** contain a compiled Lean implementation
of `forge`. No Lean compiler was available, so no actual `grind` comparison was
run. `lean/ReplayExamples.lean` is explicitly uncompiled illustrative material.
The Python checkers use exact rational arithmetic but are **not formally verified**.

The design preserves an unchanged `grind` baseline invocation in an extended
budget mode, then uses a typed obligation broker to discover useful intermediate
assertions. Proposed extensions include induction and invariant synthesis,
nonlinear cone/SOS certificates, Bernstein box proofs, typed witness generation,
selected-premise saturation, and specialized finite-domain reasoning.

## Recorded results

The latest recorded test run has **260 passing pytest cases**.

| Experiment | Restricted baseline | Extended mechanism |
|---|---:|---:|
| Polynomial cones, 60 constructed instances | 17 certificates | 60 certificates |
| Positive rational-box instances, 21 | 0 unsplit certificates | 21 subdivision certificates |
| Affine accumulator templates, 121 | Not measured | 121 synthesized/replayed |
| Out-of-template recurrences, 5 | Not applicable | 5 UNKNOWN outcomes |
| Noisy ground Horn rules, largest workload | 24,012 full-closure firings; 11,012 early-goal firings | 12 firings |

These are **controlled mechanism experiments, not Lean/grind benchmarks**.
The generated workloads intentionally exercise the new dictionary entries and
search operations. Raw timings are single warmed runs and are not statistical
speed claims. See `results/summary.json`, CSV files, `environment.json`, and
`pytest.txt` for the actual observations.

## Reproduce

The tested versions are pinned in `requirements.txt`; Python 3.13.5 was used.

```sh
python -m pip install -r requirements.txt
make test
make experiments
make pdf
```

Without `make`:

```sh
cd prototype
python -m pytest -q
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python experiments.py
cd ../article
pdflatex -interaction=nonstopmode -halt-on-error forge.tex
pdflatex -interaction=nonstopmode -halt-on-error forge.tex
```

On Windows PowerShell, environment variables can be set separately before
running the experiment script:

```powershell
$env:OPENBLAS_NUM_THREADS = "1"
$env:OMP_NUM_THREADS = "1"
python experiments.py
```

Experiments overwrite local `results/` files. Timing values can change; the
article contains rounded observations from the supplied recorded run and is
not automatically rewritten by the experiment script.

## Prototype organization

`poly.py` implements sparse exact polynomials. `cone.py` searches a bounded
nonnegative dictionary using SciPy/HiGHS, reconstructs rational weights, and
checks the resulting identity independently. `bernstein.py` produces rational
subdivision certificates and checks them by expanding the claimed Bernstein
basis. `invariant.py` synthesizes an affine fold invariant and checks the
universal base/step identities. `horn.py` performs demand slicing of finite
ground positive Horn rules and replays topological proof derivations.

The checkers take the **original target and hypotheses externally**. They must
not trust a certificate-supplied replacement problem. Example JSON files are
human-readable exports, not an audited parser/protocol; the experiments operate
on in-process typed dataclasses. Production certificate import needs bounded
parsing and resource checks.

## Limitations worth keeping

A search failure is UNKNOWN, not a disproof. The cone dictionary is not a
complete SOS procedure. Pure Bernstein positivity certificates can fail forever
on a nonzero polynomial with an irrational interior zero. The invariant grammar
covers one parameterized affine fold family, not arbitrary recursion. Ground
Horn slicing is not an implementation of E-matching modulo equality. The full
cross-engine broker and its dependent Lean integration have not been built.

The article specifies next steps, correctness contracts, practical libraries,
trust profiles, and comparative benchmarks. The inspected v4.34.0 native
computation infrastructure can introduce generated axioms, so the strict design
requires a complete dependency audit rather than a single-name blacklist.

No compiler binaries, dependency checkouts, font files, or checksum files are
included.
