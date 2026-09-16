# Resource Frontiers for Forge

Read `article.pdf` (editable source: `article.tex`, `references.tex`).

This package adds an ordinary place/transition-net lane to the inspected Forge
merged design: exact coverability frontiers for ALL initial markings, scalar
population thresholds, multiparameter unsafe Pareto frontiers, compressed runs,
positive self-covering lassos, guarded endpoint-program equivalence, and exact
productive-transition acceleration.

**This is tested Python research code, NOT an installed Lean tactic, a verified
checker, or evidence of an improvement over an existing Lean tactic.**
No Lean source was compiled in this authoring environment. The Lean integration
is specified in the article and `docs/LEAN_PORT.md`, not delivered as working code.

## Run without installing anything

Python 3.13.5 was used. The code uses the standard library only; Python 3.10+
syntax is used, but earlier interpreter versions were not tested.

```
python -m unittest discover -s prototype/tests -v
python -S prototype/replay.py results/frontiers.jsonl results/accelerated-frontiers.jsonl results/thresholds.jsonl results/parameters.jsonl results/runs.jsonl results/lassos.jsonl results/equivalences.jsonl
python -S prototype/solve.py examples/mutex.json --out my-results/mutex.json
python -S prototype/solve.py examples/broken_mutex.json --slope 1,0,0 --offset 0,1,0 --out my-results/threshold.json
python -S prototype/solve.py examples/mutex.json --family examples/population-permits.json --out my-results/parameters.json
```

The solver checks its own proposed output with the separate checker before
writing a replay record. For a second process, pass the output file to replay.py.
Exit codes: 0 = Python checked; 1 = malformed/invalid input or certificate;
2 = resource refusal/UNKNOWN. None is a Lean verification status.

`-S` disables site packages. The replay checker imports neither the producer nor
the producer's representation/arithmetic module; the replay log records this.
It is not a formally verified or fully hostile-input-hardened verifier.

## Reproduce experiments

```
python -S prototype/experiments.py --out reproduced-results
python -S prototype/equivalence_experiments.py --out reproduced-results
python -S prototype/acceleration_experiments.py --out reproduced-results
```

The first command refuses an existing output summary. Recorded evidence is
under `results/`; fresh experiments default to `reproduced-results/`.
The equivalence command writes a separate corpus in that directory.
Runtime measurements are single-run observations and vary across machines.

Results include 68 unit tests; 3,920 complete forward-oracle queries over 60
conservative nets; 1,000 word-summary comparisons; 423 replay records across
explicitly different certificate types; and named error/UNKNOWN controls.
Do not add these units into a purported solved-goal count.
The 10^100-step run is symbolically represented, not concretely executed.

A fresh offline reproduction regenerated all seven certificate corpora byte for
byte. See `results/reproduction-equality.json` and the separate fresh replay log.
Timing records were deliberately not required to be identical.

## Input semantics

A marking is a fixed-dimensional vector of natural token counts. Each step has
literal natural `consume` and `produce` vectors and fires ONLY when the input
covers `consume`. Targets are upward-closed bad patterns. These are coverability
queries, not exact-marking reachability or arbitrary liveness queries.
Negative coefficients, zero-test/inhibitor arcs, reset arcs, extra fields and
Boolean values masquerading as numbers are refused. Source programs require a
separately proved semantic bridge; a count abstraction alone does not justify a
source-level counterexample.

## Article build

Run `make article`, or run pdflatex on article.tex three times. Stock pdfLaTeX,
no shell escape and no external bibliography tool. All source files are
included; no external network dependency is required to build the article.

The baseline revision and bounded non-duplication audit are in
`docs/REVIEW_SCOPE.md`. Mathematical algorithms are not claimed as globally new.

For the optional acceleration, add `--accelerate` to solve.py. Its mathematical
contract and executed ablations are in `docs/ACCELERATION.md`. The option changes
the producer, not the certificate checker or the original transition semantics.
