# Forge with Certified Symmetry

A research extension for Vladimir Reshetnikov's Forge project, prepared September 15, 2026.

Read **article/forge-certified-symmetry.pdf**. The complete editable source is **article/forge-certified-symmetry.tex**, with section files and build script in the same directory.

## What is implemented

The standard-library Python prototype constructs and separately checks complete stabilizer-chain certificates; answers exact membership and nonmembership queries; produces complete coset-cover canonical-image certificates; recognizes symmetric and alternating groups by exact order/parity gates; computes cycle-inventory and fixed-weight orbit counts; and performs sparse Reynolds projection using checked monomial orbits. A narrow gate checks unsigned variable symmetries of concrete CNF formulas and objective weights.

The separate checker modules import no search code. All the following commands run offline from `prototype/`:

```sh
python -S demo.py
python -S -m unittest discover -s tests -v
python -S verify_corpus.py ../results/recorded
python -S verify_reynolds.py ../results/reynolds/bundles.json
```

Tested with Python 3.13.5. The executable core has **no third-party dependencies**. The optional SymPy cross-check is separate:

```sh
python optional_sympy_oracle.py
```

That supplementary script was run with SymPy 1.14.0. It corroborates seven large group orders and 140 membership answers; it is not required for normal use or replay.

## Reproduce construction, not just replay

From `prototype/`, choose new output directories:

```sh
python -S run_experiments.py --output ../reproduced-main
python -S reynolds_experiments.py --output ../reproduced-reynolds
```

The destination must not already exist. Recorded results are not overwritten. Do not use Python `-O`: regression and replay scripts require assertions and explicitly refuse optimized mode. `--skip-large` shortens the main suite but still includes its fixed S15 resource-refusal test; it does not reproduce the recorded full run.

## Results, in separate units

The main run contains 153 small-group oracle comparisons plus seven large chain instances, 8,028 membership queries, 296 generic canonical queries, 208 small family canonical queries and five large family images, 40 cycle inventories, 160 color-count comparisons, and 220 fixed-weight comparisons. There are 33 main malformed/corruption controls, five positive and ten negative CNF gates, and five expected resource refusals. Standalone replay checks all 160 main bundles.

The separate Reynolds run has 25 small comparisons against full-group averaging, 25 idempotence checks, one large S40 mixed-cubic projection over 1,560 monomials, and four malformed-projection controls. All 26 projection bundles replay without importing a producer. Twelve unittest methods also pass.

These counts overlap and have different units. They are not a pooled solved-goal count or a success rate. Full machine-readable results, certificates, and development corrections are in `results/`.

## Limits

This is **not an implemented Lean tactic**. No Lean compiler was available and no Lean-kernel certificate replay was performed. The Python checkers are not formally verified or hardened as network-facing services. The source reifier, reflected Lean checkers, automatic graph-based symmetry discovery, and adapter to Forge's cone solver remain implementation work. Generic canonical-image search can exhaust its budget; arbitrary cycle inventories still enumerate the group. The recognized-family and monomial-orbit shortcuts are separate algorithms, not evidence that those generic limits disappeared.

The article gives mathematical soundness arguments, proposed modules and APIs, primary-source library references, and source-level acceptance gates. `lean/IMPLEMENTATION.md` records the remaining formalization work. `docs/NOVELTY.md` states exactly what was inspected and the limits of the no-duplication audit.

## Build the PDF

```sh
cd article
sh build.sh
```

Or run pdfLaTeX three times on `forge-certified-symmetry.tex`. No shell escape, bibliography processor, downloaded assets, or bundled fonts are required. Only ordinary TeX Live packages are used.

The inspected Forge revision is `58ea206bd7ad501b930add568151217bcc7f82a2`. No GitHub repository was modified by this work.
