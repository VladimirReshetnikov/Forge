# Forge Beyond Finite Horizons

**Unbounded-stack summaries, recurrent strategies, and exact probabilistic termination.**

Read [`article/forge-infinite-horizon.pdf`](article/forge-infinite-horizon.pdf).
The editable master is [`article/forge-infinite-horizon.tex`](article/forge-infinite-horizon.tex);
keep it with its `sections/` directory and `references.tex`.

This is an additive proposal against Forge commit
`c98e47c5f804e92880fc1d0e378c1b95832b685c`, based on the merged capability and
provenance ledger, not a claim of an exhaustive audit of every frozen proposal.
The algorithms are classical; their certificate formats, explicit source
bridges, executable package, and experiments are the contribution here.

## What runs

Three dependency-free Python search/replay pairs:

* **Pushdown:** indexed pop-summary closure, productive DAG witnesses, closed
  exclusion certificates, and a regular-stack-target compiler.
* **Büchi games:** repeated attractors, positional policies, winning reset ranks,
  and losing ranks that bound all accepting visits.
* **Rational finite Markov chains:** exact absorption time, accumulated cost and
  terminal payoff on almost-surely absorbing instances; positive-probability
  closed-class certificates otherwise.

The checker receives the input model separately from the certificate. Search-free
replay imports no search modules. It still shares model representations, the codec,
and Python's rational arithmetic with search. It is **not formally verified**.

## What does not run

There is no installed Lean `forge` tactic in this package, no compiled Lean
checker, no automated Lean source reifier, and no Lean-kernel proof produced by
these experiments. No Lean executable was available. No comparison with `grind`,
Aesop, LeanHammer or another tactic was performed. See `docs/STATUS.md`.

The article gives exact module and theorem obligations for that implementation.
It does not include uncompiled Lean snippets disguised as completed source files.

## Reproduce

Tested with Python 3.13.5; no third-party Python packages are required.
Run from this directory:

```text
python -S -m unittest discover -s tests -v
python -S prototype/demo.py
python -S prototype/verify.py
python -S prototype/run_experiments.py
python -S prototype/verify.py reproduced-results/certificates.json
```

The experimental runner writes to `reproduced-results/` by default. Recorded
results are not overwritten. `--quick` restricts exhaustive game enumeration to
sizes 1 and 2 and therefore produces a **different** corpus. Do not use `python -O`:
reference-oracle assertions are part of the experiments.

## Recorded results

There are **36 passing named unit tests**. They include positive tests and
negative controls; this is not a count of 36 rejected mutations.

The experiment contains 881 pushdown cases, 22,300 game arenas, and 770 chains.
The game corpus includes every labelled total arena of size 1, 2 or 3, every
ownership map and every accepting set: **22,100 arenas**. The remaining 200 games
have 4–7 vertices. All 67,260 game initial vertices were replayed during the run.

The archive stores **28,566 certificate records**, all replayed successfully:
881 pushdown records, 26,915 game-region records and 770 chain records. A game
can have two nonempty regions, so records are not the same unit as arenas.
These are not counts of Lean proofs or a tactic success rate.

The 31-node compressed example represents 2,147,483,647 transitions. That run was
not expanded or executed; its length was computed from the DAG. Concrete expansion
was checked for depths through 10.

In 39 general pushdown cases the bounded concrete oracle was truncated and gave
no verdict. The exclusion certificates passed replay; they were not independently
settled by that bounded oracle. The article records this distinction explicitly.

## Build the article

With a stock TeX Live or MiKTeX installation containing pdfLaTeX:

```text
python tools/build_article.py
```

Or run `pdflatex -interaction=nonstopmode -halt-on-error forge-infinite-horizon.tex`
three times from `article/`. No shell escape, bibliography processor, or separately
installed font files are required.

## Layout

```text
article/          PDF, master LaTeX, section sources, bibliography
prototype/        three searches, separate replay, exact JSON codec, demo
results/          all recorded certificates, summary and console evidence
tests/            named controls and independent reference computations
docs/             scope, evidence status, API and source provenance
lean/             status note only: Lean implementation is not claimed
tools/            portable article build script
```

The decoder has limited size and shape controls, but is a research decoder, not a
hardened service boundary. General parity/stochastic/pushdown games, arbitrary
Lean recursion, symbolic probability parameters, and infinite-state Markov
chains are not supported by the shipped API. Proposed extensions are explicitly
labelled in the article.
