# Forge Flow

**Differential certificates, optimal cofactor ladders, and exact analytic witnesses.**

This is a research extension proposal for Forge, reviewed against commit
`c98e47c5f804e92880fc1d0e378c1b95832b685c` on 15 September 2026.
It is not an installed Lean tactic and does not modify the upstream repositories.

Read `article/forge-flow.pdf`. Its complete LaTeX source is
`article/forge-flow.tex` plus `article/sections/` and `article/references.tex`.

## Main result

For rational exponential polynomials on `x >= 0`, an exact ladder repeatedly
applies `D-c`, checks rational initial values, and ends at an ordinary polynomial
with nonnegative coefficients. Increasing cofactor order is sufficient for
feasibility in the stated input-spectrum grammar. Every nonzero rate forces its
full annihilator multiplicity; only the number of zero factors remains free.
A monotonicity theorem permits binary search for a **shortest ladder in that
grammar**, with a separately checkable minimality receipt.

The package also implements constant-Metzler-matrix differential certificates,
exact rational exponential enclosures, point refutations, and interval-specific
unique-root certificates. Read the article for proofs and exact restrictions.

## Evidence

| Outcome | Recorded cases |
|---|---:|
| Positive scalar certificates | 196 |
| Coupled-system certificates | 40 |
| Negative-point certificates | 44 |
| True functions correctly rejected by the ladder grammar | 8 |
| Unique roots inside supplied brackets | 16 |

All 624 targeted invalid mutations were rejected. There are 22 unittest methods;
200 random small problems were cross-checked by exhaustive cofactor permutations
and a breadth-first oracle; 200 derivatives were checked with SymPy 1.14.0;
161 rational exponential arguments passed a 100-digit Decimal sanity check.
These finite tests are not formal verification.

On the same 196 positive problems, shortening reduced the cofactor count from
1,212 to 288. This is **not** a Lean speedup or a comparison with `grind`.

**No Lean compilation was run.** `lean/FlowTargets.lean` contains unproved
acceptance-target proposition definitions, not proofs or a tactic. The article
specifies the missing Lean source bridge and soundness checker.

## Run without third-party packages

From the `prototype` directory:

```sh
python -S -m unittest discover -s tests -v
python -S replay.py
python -S run_experiments.py --out reproduced-results
python -S replay.py reproduced-results/certificates.json
```

Or on a POSIX shell, from the package root:

```sh
./reproduce.sh
```

The experiment runner requires a **new** output directory; it will not overwrite
an existing run. Do not use Python's `-O` option: the experiment harness uses
assertions to detect discrepancies. The core has no runtime dependency beyond
the Python standard library. It was tested on Python 3.13.5.

Optional independent diagnostics (SymPy is optional, used only here):

```sh
cd prototype
python oracle.py --out ../oracle-reproduced.json
```

## API example

```python
from forge_flow.model import ExpPoly
from forge_flow.search import optimal_ladder
from forge_flow.check import check_ladder, check_minimality

f = ExpPoly.make({0: [1], 1: [-2, 0, -1], 2: [1]})
r = optimal_ladder(f)
assert r["status"] == "certificate"
assert check_ladder(f.problem(), r["certificate"])
assert check_minimality(f.problem(), r["certificate"], r["minimality"])
print(r["certificate"]["cofactors"])
# [[1, 1], [1, 1], [1, 1], [2, 1]]
```

Each integer pair encodes a reduced rational. Coefficients and rates supplied to
the dense API must be Python integers or `fractions.Fraction` values, not floats
or arbitrary CAS scalar classes.

## Trust and non-goals

The sparse algebra checker does not import the dense model or search routines.
The numeric proposer and checker **share** the rational enclosure kernel; this is
search-independent replay, not a separately implemented numeric kernel.
The Python checkers and JSON decoding are not formally verified or hardened
against arbitrary hostile byte input. Proof acceptance in Lean still requires
proved checker soundness and equality to the original source expression.

A negative canonical anchor means **no certificate in the specified ladder
grammar**, not that the original inequality is false. A root bracket proves
uniqueness **inside that bracket**, not global uniqueness or an exact rational
root. Time/size limits returning no certificate mean unknown.

## Build the article

```sh
./build_article.sh
```

Requires pdfLaTeX and standard TeX packages. No shell escape, downloaded fonts,
or external bibliography program is needed. See `docs/STATUS.md`,
`docs/PROVENANCE.md`, and `docs/RUN_HISTORY.md` for scoped evidence and history.
