# Forge over Infinite Ordered State Spaces

A research article and executable prototype for exact unsafe-region certificates over:

* guarded nonnegative-affine natural-resource systems (including token transitions, reset, transfer, merge, and duplication);
* finite-control lossy FIFO systems with a finite alphabet and finitely many channels.

The main article is `article/forge_ordered.pdf`; its complete LaTeX source is
`article/forge_ordered.tex`. The article develops the definitions, mathematical
proofs, algorithms, source-model bridges, and detailed Lean integration plan.

## What the package does

The producers construct a finite antichain describing **every initial state from
which some finite bad execution exists**. A derivation DAG proves that the
represented states really are unsafe; complete predecessor coverage proves that
no unsafe states were omitted. The independently written checker validates both
inclusions against the entire original input model.

The eager producer computes exact local predecessor bases. The separation
producer instead searches for one predecessor not already covered by the current
global region, or returns a finite integer-box coverage receipt. It can avoid
large local Pareto bases that the global region already subsumes.

**These are Python certificates, not Lean proof terms.** No Lean executable was
available for this work. No new Lean file was compiled, no `forge` tactic was
implemented, and no comparison against `grind` was performed. Neither the Python
checker nor the source reifier has been formally verified; the reifier and Lean
checker are specified but not implemented.

## Run the software

Python 3.10+ is the intended language level; the recorded execution used Python
3.13.5. Other interpreter versions have not been tested. There are no external
Python dependencies. Run from the archive root:

```sh
python -S prototype/run_tests.py --output reproduced-results
python -S prototype/run_separation.py --source reproduced-results --output reproduced-separation
```

The first suite runs local differential tests, fully finite execution oracles,
corruption tests, cutoff controls, and fresh-process independent replay. The
second compares the two producers on the same models and exercises three large
covered-preimage examples. Each suite writes failures to its own `FAILED_RUN.txt`
if an assertion fails. Do not use `python -O`: test assertions must remain enabled.

Check an existing certificate without running any search:

```sh
python -S prototype/checker.py results/examples/semaphore.problem.json results/examples/semaphore.certificate.json
python -S prototype/checker.py results/separation/dense-8.problem.json results/separation/dense-8.certificate.json
```

Search and check an explicit model:

```sh
python -S prototype/cli.py results/examples/semaphore.problem.json --out new-region.json
```

The default engine is `separation`; use `--engine eager` for the reference
producer. The CLI refuses to overwrite existing output paths. Optional
`--initial initial.json` classifies a supplied `{"q": 0, "v": [...]}` state and
exports a checked concrete trace when it is unsafe. Exit status 2 denotes an
inconclusive search cutoff; status 1 denotes refusal or an error. Successful
output says `accepted_by_python_checker` and `lean_kernel_checked: false`.

## Recorded evidence

| Experiment | Result |
|---|---|
| Local resource predecessor problems | 1,296, with 63,504 point comparisons; zero mismatches |
| FIFO local action/word comparisons | 2,325; zero mismatches |
| Finite resource execution oracle | 100 systems, 7,000 initial-state queries; exact agreement |
| Finite acyclic FIFO oracle | 40 systems, 2,040 queries; exact agreement |
| Finite length-nonincreasing FIFO oracle | 40 systems, 2,480 queries; exact agreement |
| Eager region replay | 190 certificates accepted in a fresh process |
| Separation vs. eager | Identical exact bases on those same 190 models |
| Separation region replay | 193 certificates, including three additional dense-preimage fixtures |
| Invalid-certificate/parser controls | 32 rejected |
| Additional direct-cover controls | 5 rejected |
| Operational-cutoff controls | 4 returned unknown |

The repeated models are not additional independent systems. Point comparisons,
queries, certificates and corruption attempts are different units and are not
pooled into an overall success rate. The finite execution oracles have explicit
finiteness arguments; a reached operational bound never becomes a safety verdict.

In a constructed eight-resource example, the eager local clipping box would
contain 10,828,567,056,280,801 points and the local minimal predecessor set would
have 26,075,972,546 elements. These are formula counts, not enumerated objects.
The separation producer instead emits a two-state region certificate occupying
1,063 bytes in canonical compact JSON. The pretty-printed stored file is larger.
This is an ablation of the two delivered Python implementations, not a result
about optimized external solvers or Lean tactics.

## Layout

`prototype/` contains both producers, the independent checker, the CLI and test
runners. `results/examples/` contains ten illustrative explicit models, their
certificates and eighteen selected concrete traces. `results/corpus.json` and
`results/separation/corpus.json` retain the model/certificate replay corpora.
`results/summary.json`, `results/separation/summary.json`, logs and mutation
reports give the recorded evidence. `docs/` contains the snapshot audit, source
manifest, limitations, run history and Lean port plan.

## Rebuild the article

A TeX installation with the packages named in the source is required. No shell
escape or external bibliography processor is used.

```sh
cd article
pdflatex -interaction=nonstopmode -halt-on-error forge_ordered.tex
pdflatex -interaction=nonstopmode -halt-on-error forge_ordered.tex
pdflatex -interaction=nonstopmode -halt-on-error forge_ordered.tex
```

The original article was built with pdfLaTeX and rendered for visual inspection.
Its printed date follows the requested September 15 research snapshot; the
recorded build timestamp can be September 16 UTC.

## Scope

Classical backward coverability and WQO theory are attributed, not claimed as
new mathematics. The new-to-reviewed-Forge contribution is the specific worker
implementation/certificate design and its tested integration plan. The audit
covers the cited merged repository material, not every archived proposal.

Safety is universal finite-execution safety; unsafety is existential finite
reachability to an upward target. Reliable FIFO counterexamples, exact-word
reachability, zero tests, fairness, games, probabilities and arbitrary
higher-order source programs are outside the implemented claim. Research-code
input limits are not a security audit. See the article and `docs/STATUS.md`.
