# Analytic Proof Certificates for Forge

**Start with `article/forge-analytic-certificates.pdf`.** Its editable source is
`article/forge-analytic-certificates.tex`, with section files in `article/sections`.

This is an independent technical extension against Forge snapshot
`c98e47c5f804e92880fc1d0e378c1b95832b685c`. It does not modify that repository.
It adds analytic sign-certificate algorithms rather than repeating Forge's
existing polynomial, structural, witness, or discrete-closure architecture.

## What is developed

The exact input class is `sum P_r(x) * exp(r*x)`, with rational rates and rational
polynomial coefficients. The package implements canonical differential ladders,
bounded auxiliary-factor enrichment, explicit eventual-sign witnesses, rational
point enclosures, a reference compact interval cover, and separate receipt replay.

The article proves that ascending differential-factor order succeeds whenever
any permutation of the same multiset succeeds. Extra factors monotonically
enlarge the accepted cone. Nonzero accepted ladders are strictly positive in the
interior, so interior zeros require another route such as algebraic factoring.
A separate total mathematical procedure computes the eventual sign and an
explicit rational cutoff for every nonzero member of the exact input class.

The article also specifies proved logarithmic charts, source-reifier obligations,
Lean proof construction, exact integration milestones, and concrete reuse of
Mathlib, LeanCert, and IntervalBounds.

## Executed evidence

- 18 unit-test methods pass, including random, differential, malformed-input,
  corruption, source-substitution, domain, and strictness controls.
- 284 recorded receipts replay against separately supplied source requests with
  standard-library-only Python. These include certificates and a counterexample;
  they are not 284 independent Lean theorems.
- 14,409 factor permutations on 200 inputs give zero disagreements with the
  ascending-order acceptance criterion.
- Four auxiliary-factor examples improve over native ladders; known unknowns
  and a mathematical obstruction are retained explicitly.
- No Lean compilation or comparison with `grind` was performed.

See `results/experiment-summary.json`, `results/replay.txt`, and
`results/unit-tests.txt`. Point-enclosure search and replay share arithmetic;
the Python checkers are tested but not formally verified.

## Run

No third-party Python packages are required. Tested with Python 3.13.5.

```text
cd prototype
python -S -m unittest discover -s tests -v
python -S replay.py
python -S run_experiments.py
python -S emit_lean.py
```

The experiment generator defaults to `../reproduced-results`, preserving the
recorded results. The replay program defaults to the recorded directory. Run
`python -S replay.py --help` for a different results directory.

Example from the `prototype` directory:

```python
from forge_analytic.core import make, encode
from forge_analytic.search import ghost_search
from forge_analytic.check import verify_goal

# exp(2*x) - 4*exp(x) + 5 > 0 for every x >= 0.
p = make((2, 0, 1), (1, 0, -4), (0, 0, 5))
problem = {
    "polynomial": encode(p),
    "goal": {"kind": "positive_closed_ray", "anchor": "0"},
}
receipt = ghost_search(p)
assert receipt is not None and verify_goal(problem, receipt)
print([step["rho"] for step in receipt["steps"]])
# ['-4', '-4', '-4', '-4', '0', '1', '2']
```

`verify` checks the receipt's own mathematical conclusion against a separately
supplied polynomial. `verify_goal` additionally binds the conclusion to the
requested domain, relation, and strictness. Use the latter for source requests.

## Lean candidates

`lean/LadderBridge.lean` is a candidate integrating-factor proof; four more files
are emitted nonnegativity replays. **All are generated/uncompiled.** They contain
no intended proof holes, but no successful elaboration or axiom inventory is
claimed. See `lean/STATUS.md` for the intended baseline and compilation sequence.
The emitted nonnegativity statements are explicitly not claimed to close the
stronger strict-positive Python requests.

## Build the PDF

```text
python build_article.py
```

This uses pdfLaTeX and stock TeX packages, runs three passes, and stops on errors.
No bibliography tool, shell escape, or external font files are needed.

## Layout

`article/` contains the article and sources. `prototype/` contains all executable
code. `results/` contains retained evidence and independent source requests.
`lean/` contains candidate proof source with its explicit status. `docs/`
contains the audit and capability ledger.

No original Forge proposal, third-party implementation, font, or toolchain is
included. New source and article material are released under MIT-0; cited works
and referenced libraries retain their own terms.
