# Beyond Finite Closure: extensions for Forge

Start with **article/forge-unbounded.pdf** (31 pages). The editable root source is **article/forge-unbounded.tex**. A self-contained equivalent is **article/forge-unbounded-standalone.tex**.

This is a design delta against Forge revision `58ea206bd7ad501b930add568151217bcc7f82a2`, not another summary of its existing architecture. It develops:

* backward-antichain coverability for unbounded Petri/multiset systems;
* exact rational enclosures of least fixed points of probabilistic polynomial systems;
* inverse-free weighted Newton certificates;
* critical/subcritical extinction and isolated scalar algebraic least roots.

The package contains **executed Python algorithms and finite checkers**, not an installed Lean tactic. The paper proves their mathematical soundness in the specified fragments. No Lean compilation, source-adapter implementation, or head-to-head tactic benchmark was executed here. See `lean/IMPLEMENTATION.md` for the port boundary.

## Reproduce and replay

The prototype uses only the Python standard library. It was tested with Python 3.13.5. Its syntax requires Python 3.10 or newer; earlier supported versions were not separately tested. Do not use `python -O`: experiment assertions must remain enabled.

From `prototype/`:

```text
python -S replay.py ../results/run-01
python -S replay.py ../results/ablations-01
python -S replay.py ../results/compact-01
```

Replay actively forbids importing the producer module and optional numerical packages. The main replay checks 2,360 expected accepted receipts and 275 expected rejected records. That is a receipt count, not 2,360 unique Lean theorems.

For a fresh complete run, from the package root:

```text
python tools/validate.py
```

The helper creates a fresh timestamped directory under `reproduced/`, runs the main suite and replay, the mechanism ablations and replay, and the inverse-free conversion and replay. It compares the main receipt files against the recorded corpus. An explicit destination can be passed with `--out PATH`; it must not already exist.

Individual experiments can be invoked from `prototype/`:

```text
python -S run_experiments.py --out ../reproduced/main
python -S ablations.py --out ../reproduced/ablations
python -S compact_experiment.py ../reproduced/main --out ../reproduced/compact
```

## Small API example

Run from `prototype/` or add that directory to the module path:

```python
from fractions import Fraction as Q
from forge_unbounded.model import PPS, Term
from forge_unbounded.search import pps_enclosure, scalar_algebraic
from forge_unbounded.compact import compact_enclosure
from forge_unbounded.verify import verify

# q is the LEAST solution of q = 1/4 + 3/4 q^3.
problem = PPS(((Term(Q(1, 4), (0,)), Term(Q(3, 4), (3,))),))
receipt = pps_enclosure(problem, target_bits=24, rounding_bits=44)
assert verify(problem, receipt)
assert receipt["target_met"]

compact = compact_enclosure(problem, receipt)
assert verify(problem, compact)
# Compaction is not always a size win, particularly in dimension one.
```

The checker always receives the mathematical input independently of the receipt. The full canonical normalized input is included as its subject. This is not yet a binding to a Lean expression; a source bridge must prove that connection.

## What the evidence shows

The 2,220 finite Petri queries agree with complete forward BFS on exactly token-conserving nets. Separate examples exercise infinite reachable state spaces. Scalar quadratic systems have exact closed-form comparison values; high-precision decimal comparisons on coupled systems are diagnostics, never acceptance authorities.

The inverse-free experiment converts 100 of the existing enclosure receipts, covering 471 Newton steps. It checks 201 negative controls. Whole-receipt JSON size changes from 297,913 to 228,676 bytes overall; scalar receipts grow. These are alternative certificates for existing inputs, not additional source problems.

`results/run-02` reproduces `run-01`; their accepted and rejected corpora are byte-identical. Do not double-count those runs or combine these counts with Forge's earlier proposals.

## Build the report

With pdfLaTeX and the listed ordinary TeX packages installed:

```text
python tools/build_article.py
```

The report needs no external fonts, shell escape, or bibliography processor. Source files are split by topic and the bibliography is inline.

## Structure

* `article/`: report PDF and all editable TeX sources.
* `prototype/forge_unbounded/`: finite models, producers, checker, optional compactor.
* `prototype/*.py`: experiments, ablations, replay, and examples.
* `results/`: raw receipts, summaries, reproduction and replay records.
* `lean/`: exact implementation obligations; no placeholder proof files.
* `tools/`: portable validation and article build helpers.
* `SOURCE-AUDIT.md`: inspected repository sources and scope of novelty claims.

The Python checker is research code, shares representation/validation with the producer, and is not hardened against maliciously huge inputs. A Python acceptance is not a Lean-kernel proof. The report identifies the missing source bridges and formal soundness proofs rather than silently treating them as implemented.
