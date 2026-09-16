# Three New Engines for Forge

A technical extension study prepared for Vladimir Reshetnikov on 15 September 2026.

**Read the article:** `article/forge-extensions.pdf`  
**Edit its source:** `article/forge-extensions.tex`

The package develops three additions relative to the reviewed Forge design:

1. Exact constructive polyhedral projection for mixed strict/non-strict real linear specifications, including multiple outputs and shared min–max witness graphs.
2. Traced bounded noncommutative completion, with independent checking of two-sided ideal identities in the original relations.
3. Rational elementary-function enclosures, coverage certificates, and exact vanishing-jet proofs, including a bounded automatic anchor/order selector.

These are working Python research prototypes, **not an implemented Lean `forge` tactic**. No Lean compiler was available for this execution; all files in `lean/` are explicitly uncompiled. Mathematical soundness arguments and the concrete Lean integration work are described in the article.

## Recorded results

| Workload | Cases | Positive Python receipts | Refutations | Unknown |
|---|---:|---:|---:|---:|
| Polyhedral | 110 | 79 | 30 | 1 |
| Noncommutative | 85 | 82 | 0 | 3 |
| Analytic | 44 | 37 | 0 | 7 |

All expected outcomes were obtained. The analytic positives are 33 interval certificates and four manually selected jet profiles. Automatic discovery subsequently found certificates for the same four jet goals (orders 2, 2, 2, 3); those overlapping results are stored separately and are not added to the case totals.

Additional evidence: 180/81/81 rejected mutations in the three lanes; 160 exact vertex-oracle comparisons; 288 Weyl polynomial actions; 490 witness evaluations; twelve passing named unit tests. Optional numerical sanity checks cover 320 elementary-function point evaluations. None is a Lean-kernel receipt or a head-to-head tactic benchmark.

## Run without third-party packages

Python 3.13.5 was used for the recorded execution. From the archive root:

```sh
cd prototype
python -S verify.py
python -S verify.py ../results/jet-discovery.json
python -S -m unittest discover -s tests -v
python -S run_experiments.py --out reproduced-results
python -S discover_jets.py --out reproduced-jets.json
```

`verify.py` prohibits imports of search and witness-proposal modules during replay. `-S` disables site packages. The default experiment output is a new directory, not the recorded `results/` directory.

For the optional numerical sanity check only:

```sh
python -m pip install -r requirements-optional.txt
python numerical_crosscheck.py --out numerical-crosscheck.json
```

The optional script is never invoked by certificate acceptance.

## Build the PDF

Use a reasonably complete TeX Live or MiKTeX installation:

```sh
cd article
pdflatex -interaction=nonstopmode -halt-on-error forge-extensions.tex
pdflatex -interaction=nonstopmode -halt-on-error forge-extensions.tex
pdflatex -interaction=nonstopmode -halt-on-error forge-extensions.tex
```

No shell escape, bibliography processor, or font-file download is needed. Standard `newpx`, `microtype`, `tcolorbox`, and related TeX packages are used.

## Where to look

`prototype/forge_delta/` contains the searchers and independent checkers. `prototype/tests/oracles.py` contains the separate exact vertex and operator-action oracles. `results/certificates.json` stores every original problem alongside its certificate or unknown outcome. `results/summary.json` and `results/measurements.csv` hold environment, counts, and local timing/size measurements. `results/jet-discovery.json` is the overlapping automatic-jet profile. `docs/STATUS.md` records implementation boundaries; `docs/sources.json` records source pins.

The `prove` entry points are untrusted proposers. Never interpret a returned tag as source-level authority without checking the original problem. The checkers are research code and are not hardened against hostile, resource-exhausting inputs.

## Repository snapshots

Forge: `c98e47c5f804e92880fc1d0e378c1b95832b685c`  
Leant: `6bf05ad78c467989e68290f2d08bbed40802d485`  
Djex: `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`

The archive contains newly authored material, not copies of the prior Forge submissions. Referenced projects and publications retain their original terms. New material is supplied under MIT-0; see `LICENSE`.
