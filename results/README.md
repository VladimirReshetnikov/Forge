# Results

Recorded evidence from the thirty-six prototype runs — the design round
`p1`..`p9`, the extension round `e1`..`e9`, the third round `r1`..`r9`, and the
fourth `s1`..`s9` — plus the measurements this merge was able to add.

## Where the evidence lives

**The thirty-six original runs stay where they were recorded**, under
`proposals/<slug>/results/`. They are not copied here and not edited. Each run
is a self-contained record of one execution — its own seed, its own generators,
its own case set, its own byte-identical duplicate files — and rewriting any of
it would destroy the thing that makes it evidence.

This directory holds only what is *derived* from those runs, plus new results.

```
results/
  README.md                     this file
  manifest.json                 one row per run: environment, seed, counts,
                                Lean status, where the raw files are
  certificate-counts.csv        per run, per family — never a bare total
  lean-core-elaboration.json    NEW: 3 merged-tree design files elaborated
  lean-closure-elaboration.json NEW: 3 merged closure files elaborated
  lean-extensions-elaboration.json  NEW: 10 extension files elaborated
  extension-suites-rerun.json   NEW: all nine extension suites re-run here
  round-three-suites-rerun.json NEW: all nine third-round suites and eight
                                replay corpora re-run here
  lean-round-three-elaboration.json  NEW: 2 elaborated, 1 failed, with the
                                diagnosis and a tested repair
  round-four-suites-rerun.json  NEW: round four's suites and replay corpora
  lean-round-four-elaboration.json  NEW: 2 elaborated, plus a defect found in
                                our own sorry scan and the 88-file audit it
                                made possible
```

## The non-pooling rule

The thirty-six runs are **not comparable and must never be summed** — not
within a round, and not across the four rounds.

This needs saying loudly because they look comparable. All nine design-round
runs ran on 2026-09-14, on Python 3.13.5 / NumPy 2.3.5 / SciPy 1.17.0 / SymPy 1.14.0 under
Linux, and five of them recorded the same seed value, `20260914`. That
coincidence is a trap. The same seed drives entirely different generators over
entirely different case sets:

| Run | What seed `20260914` actually generated |
| --- | --- |
| p3 | 30 cone + 60 quadratic cases |
| p4 | 1,080 witness tables + 300 CDCL(T) instances |
| p5 | 100 cone + 49 invariant cases |
| p6 | 1,500 differential SAT cases |
| p7 | 26 curated certificates |

Three runs — p1, p8, p9 — record no seed at all.

The extension round repeats the coincidence almost exactly: all nine ran on
Python 3.13.5 under Linux 6.18.44, and five of them (`e1`, `e2`, `e3`, `e4`,
`e6`) recorded the seed `20260915` — one day later, one digit different. `e5`
used `2026091507`, `e9` used `681437`. It is the same trap for the same reason.

The third round repeats it once more, and now across rounds: four of its nine
(`r3`, `r4`, `r7`, `r9`) recorded `20260915`, which is the extension round's
shared value. The same integer therefore labels runs in two different rounds
over entirely unrelated generators — polyhedral cases, exponential-polynomial
ladders, Markov decision processes and pushdown systems. It has stopped being a
coincidence worth explaining and become a standing hazard.

The fourth round finishes the pattern: **seven of its nine** record
`20260915` as well. Sixteen runs across three rounds now carry that one integer
over sixteen unrelated generators — Petri nets, real-root covers, binary
automata, permutation groups, chain complexes, and more. Two proposals defuse it
in their own text. The rest do not. A matching seed here is not evidence of a
shared corpus.

Round four also contains three traps worth knowing before quoting any of its
numbers. Two proposals ship superseded runs that reproduce their own headline
totals and say not to add them. One proposal's `643` appears twice inside itself
— as its witness count and as a mutation class inside its 1,096 — so quoting
both is right and adding them is not. And two proposals each report exactly
twelve unit tests whose lists share no name and no subject.

Across the rounds there is a second reason not to add anything up. The extension
proposals were written *against the merged design*, and several of them
re-derive results the design round had already recorded — polynomial invariants,
telescoping, integer witnesses — in a stronger certificate language. A
cross-round total would count the same mathematics twice under different unit
names. Every extension package states the rule for itself; two of them say in so
many words that their counts must not be appended to a historical solved-goal
total.

The units differ too. "Cases", "checks", "assertions", "tests", "certificates"
and "bundles" are five different things, and several runs use more than one. One
run states the rule for itself in the sharpest available form: *do not divide
1,238 by 1,494 and advertise an overall accuracy*, because that denominator
mixes proof searches, model searches, a lemma batch, deliberately false
formulas, and overlapping ablation runs.

Every derived file here therefore carries a `run` column, and
`certificate-counts.csv` never emits a grand total.

## Two properties that do hold across all nine design-round runs

**Exact rationals everywhere.** No mathematical coefficient anywhere in the
certificate corpus is a float. A scan of every payload in all nine runs found
exactly one floating-point number, and it is a timing field. Eight runs
serialise rationals as strings (`"125/18"`); one uses integer
numerator/denominator objects. That is the only numeric conversion any
translation layer needs.

**Search-free replay.** Every run's stored certificates replay under a
standard-library-only checker, verified with site packages disabled.

Both properties hold in the extension round too, with one qualification that
belongs here rather than in a footnote. "Replays without the search" means three
different things across these packages, and they are not equivalent:

| Strength | What replay actually does | Where |
| --- | --- | --- |
| Strongest | The checker performs a genuinely different computation from the search | `e7` ideal lane, `e9` all lanes |
| Middle | Search entry points are replaced by exceptions before replay; input-table semantics still shared | `e8` invariant and finite lanes |
| Weakest | The checker reconstructs the answer with *the same assembler* the search used | `e8` integer projection |

The third is disclosed by the package that built it: replay there detects a
modified receipt or program but cannot detect an arithmetic mistake common to
both uses of the assembler. It is mitigated by an exhaustive concrete oracle
over a provably sufficient range, not by checker independence. Anyone quoting a
"all certificates replay" figure across this repository should say which of the
three they mean.

## The Lean result

Three files are new. All eighteen proposals recorded their Lean status as
`NOT_RUN` — no toolchain in any authoring environment — under a dozen different
filenames and several formats. This merge installed the pinned
`leanprover/lean4:v4.34.0` and elaborated every file that imports nothing beyond
Lean core: three design files in the merged tree (`lean-core-elaboration.json`),
ten across the extension proposals (`lean-extensions-elaboration.json`), and
three that this merge wrote by deduplicating those ten
(`lean-closure-elaboration.json` — the ten contained six spellings of one
reachability theorem and five of one word-fold theorem).

All sixteen elaborate, and ten of them print `does not depend on any axioms` for
every theorem they expose. That is the whole claim. It is not an axiom audit, it says nothing about the twenty-one
Mathlib-dependent files, it does not establish that any checker is correct, it
is not a comparison against any tactic, and it does not change what any of those
files says.

See [`../docs/LEAN-STATUS.md`](../docs/LEAN-STATUS.md).

## The extension re-run

`extension-suites-rerun.json` is the other new measurement, and it is the one
the design round could not have. The nine design-round authoring environments
were unavailable here, so their recorded counts could only be read. Every
extension suite *runs* here, and all nine reproduce their recorded counts.

That is a reproduction on different versions — Python 3.14.4 rather than 3.13.5,
with newer NumPy, SciPy and pytest — not a bit-identical replay. No timings were
compared. It establishes that the suites pass and that the recorded counts are
accurate. It establishes nothing about checker correctness, and it is not a Lean
result.

## The merged package is a nineteenth run, not a fraction of a total

`prototype/` is a single package assembled from the eighteen codebases: the
design round's algorithm families, plus the five extension-round closure lanes
that are standard library only. It has its own test suite and its own
certificate corpus, and those numbers belong to it alone:

| | |
| --- | --- |
| `python -m pytest -q` | 748 passed |
| `python -S bin/verify.py` | 33 certificates rechecked, 50 mutations rejected |
| Environment | Python 3.14.4, NumPy 2.4.4, SciPy 1.17.1, SymPy 1.14.0 |

That environment differs from the eighteen runs' (Python 3.13.5, NumPy 2.3.5,
SciPy 1.17.0), so even the families it inherits unchanged are a fresh
observation rather than a reproduction. The 748 is a merged suite: it is not the
sum of the eighteen suites, and several source assertions did not survive the
merge because they pinned counts that depended on one proposal's own search
grammar.

Two extension lanes are *not* folded in. Target-generated ideal closure needs a
Gröbner engine and boundary-safe telescoping needs exact bivariate nullspaces,
so neither search can be standard-library-only, and folding them in would cost
the package the property that makes its replay evidence worth anything. They
stay under `proposals/e1`, `e3`, `e6`, `e7` and `e9`, run from there, and their
counts are theirs.

The 33 certificates are a deliberately small regression corpus covering every
family once, not a re-run of any proposal's benchmark. Eleven of them are the
closure families, and six of those are negative: two separating words, a
constructor counterexample and three Kripke countermodels. They are results,
not failures. Nothing here supersedes
the recorded runs, and nothing here should be compared against them.

## Re-running

Experiments write to `reproduced-results/`, which `.gitignore` excludes, so a
re-run cannot overwrite a recorded one. Compare, do not replace.

Timings will differ: every run's own notes say so, and several explicitly
decline to infer a speedup from them. One run recorded a *slower* configuration
with *fewer* rule firings and refused to report a ratio; another found two SAT
solvers taking the same ~26 ms despite a 2.5× difference in decision counts.
Operation counts are the interpretable quantity here. Wall-clock is not.
