# Forge Automatic Arithmetic

A concrete research extension to Forge: first-order arithmetic on **unbounded natural numbers**, binary-automatic predicates, exact certificate replay, and regular least-witness graphs.

Start with [`article/forge-automatic-arithmetic.pdf`](article/forge-automatic-arithmetic.pdf). Editable LaTeX is split across the main `.tex`, `sections/`, `named-table.tex`, and `references.tex`.

## What is delivered

The standard-library-only Python producer compiles linear equalities, inequalities, congruences, popcount parity, powers of two, and bitwise AND/XOR relations under Boolean operations and arbitrary first-order quantifier nesting. Correct existential projection includes zero-tail saturation, so hidden witnesses can have more digits than the visible inputs. The same compiler builds regular **least-witness** graphs and evaluates them on arbitrarily large natural inputs.

The checker is separately implemented. It imports neither producer nor formula helpers, performs no graph exploration or minimization, and checks local construction equations against a separately supplied expected query. It is research Python, **not a formally verified Lean checker**.

**No Lean tactic, compiled Lean proof, or comparison with `grind` is delivered.** The article specifies the Lean theorem stack, source-expression bridge, libraries, and acceptance milestones. Existing automata theory and Sheng's Lean automata formalization are credited; no global novelty claim is made for automata-based arithmetic.

## Reproduce

Tested with Python 3.13.5; no pip installation or third-party package is needed.

```sh
cd prototype
python -S replay_all.py ../results/run1
python -S -m unittest test_interfaces
python -S experiments.py --out ../reproduced-results
```

Choose a new output directory for experiments; an existing directory is overwritten. Do not use `python -O` for the experiment harness, which uses assertions. The checker itself uses explicit rejection checks.

Search-free replay returns acceptance of **90 construction certificates and 643 witness traces**. The 90 certificates comprise 25 named queries, 60 guarded alternating formulas, and 5 witness-relation graphs; these are not 90 independent theorem families. A function graph need not hold for every input/output pair, so a graph bundle may include a counterexample to its universal closure without indicating a failed synthesis.

One-certificate workflow:

```sh
python -S producer.py ../results/run1/queries/successor_cut.json ../cut.json
python -S checker.py ../results/run1/queries/successor_cut.json ../cut.json
```

The producer supports `--max-states N` and `--no-minimize`. Budget exhaustion produces `unknown`, never a false verdict. The checker rejects `unknown` as proof evidence.

## Recorded evidence (run 1, not pooled across runs)

| Experiment | Result |
|---|---:|
| Named queries | 20 true and 5 false, all as expected |
| Quantifier-free oracle comparisons | 46,080 across 180 automata |
| Additional zero-padding evaluations | 92,160 |
| Guarded alternating formulas | 60; 27 true and 33 false |
| Complete guarded oracle leaves | 6,480 |
| Concrete least witnesses | 643 accepted; 12 expected absence results |
| Large-input witness records | 15 |
| Smaller-candidate oracle checks | 37,124 |
| Intentionally corrupted objects rejected | 1,096 |
| Broken-projection regressions | 8 fail naively, all 8 corrected |
| Budget unknown controls | 4 |
| Separate interface tests | 7 |

Run 2 repeats the complete suite after a fresh-name guard improvement and reproduces all summary counts. Do not add its counts to run 1. The first failed budget fixture and its diagnosis are retained under `results/history/` and `docs/RUN_HISTORY.md`.

## Files

- `prototype/formula.py`: explicit syntax and capture-avoiding least-graph construction.
- `prototype/producer.py`: exact automata compiler, quotient receipts, verdicts, witness evaluator.
- `prototype/checker.py`: independent local replay and concrete witness checks.
- `prototype/experiments.py`: deterministic generated corpus and mutation/ablation controls.
- `prototype/replay_all.py`: fresh-process search-free corpus replay.
- `prototype/test_interfaces.py`: seven focused interface controls.
- `prototype/example.py`: runnable large-input least-witness example.
- `results/run1/` and `results/run2/`: full query/certificate corpora and recorded measurements.
- `docs/SCHEMA.md`: wire-format semantics and caveats.
- `docs/PORTING.md`: proposed Lean integration gates.
- `docs/SOURCES.md`: source review and provenance.

## Build the article

```sh
cd article
pdflatex -interaction=nonstopmode -halt-on-error forge-automatic-arithmetic.tex
pdflatex -interaction=nonstopmode -halt-on-error forge-automatic-arithmetic.tex
pdflatex -interaction=nonstopmode -halt-on-error forge-automatic-arithmetic.tex
```

Stock TeX Live packages; no bibliography tool, shell escape, external fonts, or external images are required.

## Boundaries

The domain is `Nat`, with linear expressions interpreted in `Int`. Signed coefficients are not truncated natural subtraction. Variable multiplication, the binary exponentiation graph, arbitrary recursive predicates, integer quantification, dependent-type reification, and a public alternating-strategy compiler are not implemented. A regular graph is not automatically a one-pass streaming transducer: the evaluator uses forward dynamic programming and backtracking. Resource checks are not a hostile-input security audit. Full scope and mathematical proofs are in the article.
