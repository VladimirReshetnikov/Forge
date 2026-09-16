# Exact Infinite-State Workers for Forge

Read **[the 29-page article](article/forge-infinite-state.pdf)** or build its
[LaTeX source](article/forge-infinite-state.tex).

This package proposes two new Forge workers and implements them, plus their
composition, as executable Python research prototypes:

* Backward antichains for finite-control, unbounded counter systems, including
  nonnegative affine families of initial markings.
* Exact joint-equality-orbit equivalence for deterministic equality-register
  transducers over arbitrary names.
* A combined equality-register/counter safety worker whose certificates are
  checked against the original mixed-rule model, not a trusted compiled graph.

The algorithms have classical foundations. Their restricted semantics,
certificates, source bridges, and integration with Forge are the contribution
of this package. The article names the nearest existing Forge capability rather
than repeating the repository's architecture.

## Run

Python 3.10+; no pip packages needed. The recorded run used Python 3.13.5.
Commands work from the package root in a shell or PowerShell.

```text
python -S tests/test_core.py
python -S prototype/replay.py
python -S prototype/run_experiments.py --output reproduced-results
```

Use a worker on an individual JSON model:

```text
python -S prototype/forge_worker.py search vass examples/mutex.model.json --output candidate.json
python -S prototype/forge_worker.py check vass examples/mutex.model.json --certificate candidate.json
python -S prototype/forge_worker.py search nominal examples/lru_fifo.model.json
python -S prototype/forge_worker.py search mixed examples/owner_pool.model.json
```

`search` validates inputs and rechecks every conclusive producer result.
`check` imports no producer. A nominal model file is an array of two machines.
Exit status 0 means a checked *model* result, including a valid negative witness;
2 means unknown; 1 means an input/checking error. Nothing here installs a Lean
tactic or publishes a Lean proof.

## Recorded evidence

| Family | Random cases | Positive | Negative | Exhaustive-oracle agreement |
|---|---:|---:|---:|---:|
| Counter systems | 300 | 222 | 78 | 300/300 |
| Equality-machine pairs | 160 | 123 | 37 | 160/160 |
| Mixed systems | 180 | 116 | 64 | 180/180 |

All 37 nominal negative cases also agree on shortest witness length.
The retained corpus contains these 640 cases plus ten named examples: **650
objects**. Standalone checker-only replay accepts all of them. The unit suite
has **27 methods**. There are **1,300 rejected structural/required-content
mutations**, not 1,300 independent deep semantic attacks.

The random systems are deliberately small. Their finite oracles share the
checker's concrete interpreter, but not the producers' algorithms. These are
regression/differential results, not evidence of performance against Lean tactics.

The cache example returns `0, 1, 0, 2, 0` as a shortest LRU/FIFO distinction;
exhaustive testing over just two keys misses it. The mixed owner example checks
arbitrarily many waiting clients; its faulty version has a two-name, two-step
counterexample at an initial waiting count of two.

## Files

`prototype/checker.py` is the search-independent research checker.
`antichain.py`, `nominal.py`, and `mixed.py` implement the producers.
`oracles.py` implements finite concrete BFS oracles.
`fixtures.py`, `run_experiments.py`, and `tests/test_core.py` reproduce the tests.
`results/` retains models, certificates, outcomes, and logs.
`examples/` exports the ten named models and their certificates.
`lean/CounterLemmas.lean` is a small **uncompiled** arithmetic/step specimen,
with no `sorry`, not a verified checker or an implemented tactic.

## Build the article

```text
python build.py
```

Requires `pdflatex` with the standard packages listed in the LaTeX preamble.
No shell escape, downloaded fonts, or external bibliography tool is needed.
The build writes TeX intermediate files inside `article/`.

See [STATUS.md](docs/STATUS.md) for proof boundaries,
[INTEGRATION.md](docs/INTEGRATION.md) for next implementation steps, and
[SOURCES.md](docs/SOURCES.md) for pinned repository identities.
