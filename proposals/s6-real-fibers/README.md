# Forge: Uniform Real-Fiber Certificates

**A concrete capability extension, not an installed Lean tactic.**

Start with [the 30-page article](article/forge-real-fibers.pdf). Its complete LaTeX
source is [article/forge-real-fibers.tex](article/forge-real-fibers.tex), with the
included `article/sections/` files. The article contains the mathematical proofs,
a repository-relative novelty audit, concrete library and integration plans,
experiments, limitations, and references.

## What this adds

The proposed worker counts **distinct real solution tuples** of a monic triangular
polynomial system subject to an arbitrary Boolean combination of polynomial-sign
conditions. Its result is a finite polynomial-sign/count circuit that remains
valid at repeated roots and exceptional parameter values. Existence, uniqueness,
and universal properties of a finite fiber can be reduced to these counts.

The package implements three related pieces:

1. Uniform symbolic real-fiber counts, using goal-directed sign indicators,
   weighted Hermite trace matrices, and characteristic-polynomial signatures.
2. Complete closure of one remaining real parameter by checked sections and
   sectors, including isolated irrational parameter values and both infinite tails.
3. Exact algebraic witness descriptors for the supported concrete univariate
   fragment, checked against the source equation and every requested atom.

These are classical mathematical ingredients assembled into a new proposed Forge
capability. This is not a claim to have invented Hermite forms, Sturm theory, or
real quantifier elimination. Forge already has fixed-interval Sturm certificates
and many other arithmetic and planning workers; those are prerequisites rather
than contributions here. See `docs/REPOSITORY_AUDIT.md` and article Section 1.

## Replay without third-party packages

From the archive root, with Python available:

```sh
python -S prototype/bin/replay.py results/run-02
```

This reruns all final stored valid bundles, specialization comparisons, corrupted
bundles, Boolean fixtures, and matrix fixtures. An import guard also refuses
SymPy, NumPy, FLINT, and the producer. `-S` disables site-package initialization.
Run without `-O`: the test runner uses assertions for some fixture comparisons.

Run the focused unit suite separately:

```sh
cd prototype
python -S -m unittest discover -s tests -v
```

The recorded environment was Python 3.13.5 on Linux. Other versions have not been
qualified by this package.

## Regenerate a fresh corpus

From the archive root:

```sh
python -m pip install -r prototype/requirements.txt
python prototype/bin/run_experiments.py --output reproduced-results
python -S prototype/bin/replay.py reproduced-results
```

The generator uses SymPy 1.14.0 and seed 20260915. It refuses to overwrite a
nonempty output directory. The final recorded corpus is `results/run-02`;
`results/run-01` is an earlier, smaller successful run and is retained as history.
Do not pool the runs. Wall times and timestamps vary across runs and environments.

## Recorded evidence

| Category | Final recorded result |
| --- | --- |
| Quantified one-parameter problems | 19, over 113 cells; 16 true and 3 false expected verdicts |
| Valid stored bundles | 99 |
| Exact count comparisons | 748 |
| Boolean indicators | 160 formulas, checked on 4,800 sign assignments |
| Exact matrix-signature fixtures | 90 |
| Algebraic witnesses | 6 |
| Invalid mutations | 973 rejected |
| Focused unit tests | 25 passed |

These are distinct units, not numbers to add into a single proof count. The 748
comparisons comprise 578 samples of universal one-parameter families, 98 samples
of two-parameter families, 48 concrete univariate problems, and 24 triangular
problems. Two-parameter uniform certificates were checked, but no complete
two-dimensional parameter-space closure was implemented.

Authoritative machine-readable records are `results/run-02/summary.json` and
`results/replay-run-02.json`. Detailed per-case objects are in
`results/run-02/certificates/`, with mutation and fixture corpora alongside them.
The initial unit-test error log is retained and explained in
`docs/RUN_HISTORY.md`; no acceptance condition was weakened to fix the tests.

## Trust and scope

* No new certificate in this package was checked by Lean's kernel. No Lean
  executable was available for the new work. The article's proposed Lean modules
  and theorem dependencies are an implementation plan, not tested Lean code.
* The Python checker is not formally verified or hardened against hostile input.
  Producer and checker use different core computations but share representation
  and some admission/outer-cover code. The article details common-mode risks.
* The implemented source fragment is a monic triangular finite algebra. It is
  not a decision procedure for arbitrary semialgebraic systems. Size limits,
  unsupported source forms, and exhausted searches must remain failure/unknown,
  never a false theorem verdict.
* A checked false verdict for an admitted, completely covered quantified source
  is different from search failure. It must not be exported as a counterexample
  to a Lean source expression without the exact source-equivalence bridge.
* There is no head-to-head comparison against `grind`, Aesop, `nlinarith`, or any
  other tactic. There is no measured Lean speedup or solved-goal gain.

## Files

```
article/       PDF, main LaTeX source, section sources and bibliography
prototype/     exact replay library, SymPy producer, runners and unit tests
results/       both retained corpora, final replay record and test logs
docs/          source audit, status and run history
```

`prototype/real_fibers/checker.py` exposes `verify(source, certificate)`;
`producer.py` exposes `make_problem(...)` and `produce(source)`.
`outer.py` and `witness.py` expose `verify_outer` and `verify_witness`.
Source ownership matters: an integration must obtain `source` from its own
request, not trust a replacement source attached by a certificate sender.
The article gives an executable minimal API example and all schema details.

## Build the article

A standard pdfLaTeX installation with the packages named in the source is enough:

```sh
cd article
pdflatex -interaction=nonstopmode -halt-on-error forge-real-fibers.tex
pdflatex -interaction=nonstopmode -halt-on-error forge-real-fibers.tex
```

The final delivered PDF has 30 pages. No external repository code, third-party
papers, binary tools, or font files are redistributed in this archive.
