# Results

Recorded evidence from the nine prototype runs, plus the one measurement this
merge was able to add.

## Where the evidence lives

**The nine original runs stay where they were recorded**, under
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
  lean-core-elaboration.json    NEW: the only compilation evidence in the repo
```

## The non-pooling rule

The nine runs are **not comparable and must never be summed.**

This needs saying loudly because they look comparable. All nine ran on
2026-09-14, on Python 3.13.5 / NumPy 2.3.5 / SciPy 1.17.0 / SymPy 1.14.0 under
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

The units differ too. "Cases", "checks", "assertions", "tests", "certificates"
and "bundles" are five different things, and several runs use more than one. One
run states the rule for itself in the sharpest available form: *do not divide
1,238 by 1,494 and advertise an overall accuracy*, because that denominator
mixes proof searches, model searches, a lemma batch, deliberately false
formulas, and overlapping ablation runs.

Every derived file here therefore carries a `run` column, and
`certificate-counts.csv` never emits a grand total.

## Two properties that do hold across all nine

**Exact rationals everywhere.** No mathematical coefficient anywhere in the
certificate corpus is a float. A scan of every payload in all nine runs found
exactly one floating-point number, and it is a timing field. Eight runs
serialise rationals as strings (`"125/18"`); one uses integer
numerator/denominator objects. That is the only numeric conversion any
translation layer needs.

**Search-free replay.** Every run's stored certificates replay under a
standard-library-only checker, verified with site packages disabled.

## The Lean result

`lean-core-elaboration.json` is new. All nine proposals recorded their Lean
status as `NOT_RUN` — no toolchain in the authoring environment — under five
different filenames and in two formats. This merge installed the pinned
`leanprover/lean4:v4.34.0` and elaborated the three files that import nothing
beyond Lean core.

All three elaborate. That is the whole claim. It is not an axiom audit, it says
nothing about the thirteen Mathlib-dependent files, it does not establish that
any checker is correct, and it is not a comparison against any tactic.

See [`../docs/LEAN-STATUS.md`](../docs/LEAN-STATUS.md).

## Re-running

Experiments write to `reproduced-results/`, which `.gitignore` excludes, so a
re-run cannot overwrite a recorded one. Compare, do not replace.

Timings will differ: every run's own notes say so, and several explicitly
decline to infer a speedup from them. One run recorded a *slower* configuration
with *fewer* rule firings and refused to report a ratio; another found two SAT
solvers taking the same ~26 ms despite a 2.5× difference in decision counts.
Operation counts are the interpretable quantity here. Wall-clock is not.
