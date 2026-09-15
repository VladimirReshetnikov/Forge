# Forge: Finite Certificates for Infinite Behaviors

A technical extension report and three working Python search prototypes for
[VladimirReshetnikov/Forge](https://github.com/VladimirReshetnikov/Forge).

Read **`article/forge-finite-certificates.pdf`**. Its complete LaTeX sources are
in the same directory. The report develops new concrete workers rather than
repeating Forge's existing controller and certificate architecture.

## Implemented capabilities

**Inductive ideals.** A degree-bounded descending-space algorithm finds families
of polynomial equations preserved collectively, with polynomial multipliers
and equality guards. It extracts original-generator identities using tracked
Buchberger computations. This strictly extends the conservation-only ansatz on
the discriminating examples in the corpus.

**Weighted residual closure.** Exact rational reachable-space search decides
zero equivalence of finite weighted representations, returning either finite
closure matrices or an independently checkable distinguishing word. It includes
an affine/tensor example proving equality of two different word-counting folds.

**Pole-safe telescoping.** A bounded coefficient ansatz discovers recurrences
for sums of powers of binomial coefficients. Its checker verifies polynomial
identities, explicit support boundaries, leading-coefficient nonvanishing, and
initial values. It recovers the binomial first-power, square, and cube (Franel)
recurrences. It is not a complete general Zeilberger implementation.

## Recorded status

The executed corpus has **82 attempts**: 27 ideal certificates, 23 weighted
closure certificates, 25 distinguishing words, 3 telescopers, and 4 unknown
results from bounded searches. All **78 returned artifacts** pass independent
standard-library replay. The pytest suite reports **318 passed**, including
148 rejection controls and 84 differential cases.

**There is no implemented Lean tactic in this package.** The two Lean files
are explicitly **NOT_RUN** specimens. No Lean or Lake executable was available
in the authoring runtime. The Python receipts are not Lean-kernel proofs; the
article identifies the source bridges and generic Lean theorems still to write.
No head-to-head tactic benchmark was run. The written soundness proofs concern
the specified certificate languages.

## Reproduce

Use Python **3.10 or newer**. The recorded run used Python 3.13.5, SymPy 1.14.0,
and pytest 9.0.2 on Linux x86-64. From this directory:

```text
python -m pip install -r requirements.txt
python -m pytest -q
python -S replay.py
python run_experiments.py --out reproduced-results
python -S replay.py reproduced-results/certificates.json
```

The `-S` replay invocation disables Python's site packages: `prototype/check.py`
uses only the standard library and does not import SymPy or the search workers.
Generation uses SymPy. The search workers do not import the checker.

The experiment generator writes to `reproduced-results/` by default. It leaves
the supplied recorded measurements intact. Times are single local measurements,
not performance promises or a theorem-proving success rate. Random families
are seeded and intentionally constructed to have known mathematical behavior.

## A minimal programmatic example

```python
import sympy as s
from prototype.ideal import discover
from prototype.check import verify

x, y, t = s.symbols("x y t")
answer, info = discover(
    variables=(x, y),
    initial=[((t,), [t, t**2])],
    transitions=[([x**2, y**2], [])],
    goal=x**2 - y,
    degree=2,
)
if answer is None:
    print("Unknown:", info)
else:
    problem, certificate = answer
    receipt = verify(problem, certificate)
    print(info["invariants"])  # ['x**2 - y']
    print(receipt)
```

The corresponding identity is
`(x**2)**2 - y**2 == (x**2 + y)*(x**2 - y)`, not conservation of `x**2-y`.
All substitutions in the search are simultaneous.

Other entry points are `prototype.weighted.discover(alpha, matrices, beta)` and
`prototype.telescoping.discover(power, order, coefficient_degree,
numerator_degree)`. The weighted API uses **row vectors** for the initial state
and column vectors for the output. `weighted.subsequence_identity()` constructs
the worked example. A `None` search result is inconclusive. The ideal search
raises `BudgetExceeded` on explicit resource cutoffs.

## Contents

- `article/`: PDF, main `.tex`, section files, bibliography source.
- `prototype/`: search algorithms, search-side encoder, independent checker.
- `tests/`: replay, mutation, and differential tests.
- `results/`: original problems, certificates, measured outcomes, pytest logs,
  independent replay output, and explicit status.
- `lean/ProofPrinciples.lean`: uncompiled generic reachability/word simulation.
- `lean/ReplayTargets.lean`: uncompiled concrete Mathlib polynomial identities.
- `docs/`: snapshot and implementation notes.

## Build the article

With an ordinary TeX Live installation, run the following command three times
from `article/`:

```text
pdflatex -interaction=nonstopmode -halt-on-error forge-finite-certificates.tex
```

The supplied Makefile also provides `make article`, `make test`, and `make replay`.
It is optional; the Python and LaTeX commands work without Make. New TX fonts
are referenced through the installed TeX packages, not bundled as font files.

## Lean specimens

The specimens have no unfinished proof placeholders, but have **not** been
compiled. `ProofPrinciples.lean` imports core Lean; `ReplayTargets.lean` imports
Mathlib. Compile them inside a separately configured Lean/Mathlib project using
`lake env lean <path>`. Keep the `NOT_RUN` status until a real build succeeds.
The report uses Forge's recorded Lean 4.34.0 / Mathlib commit as the proposed
baseline; the online API documentation was consulted separately and can evolve.

## Input and security scope

Certificate inputs are versioned data, never evaluated Python or Lean source.
The checker rejects floating-point coefficients, duplicate JSON keys, malformed
rational encodings, missing transition inventories, and failed identities. It
has size and dimension limits, but is a research checker, not a hardened network
service. Intermediate arithmetic can be expensive; production use needs separate
process, time, and memory budgets. Unsupported or malformed input must never be
promoted to a proof or a source-level counterexample.

Original code and report source are provided under MIT-0. External tools,
repository content, and fonts are not bundled and retain their own licenses.
