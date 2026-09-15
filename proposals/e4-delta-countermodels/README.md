# Forge Delta

**Exact observable closure and constructive countermodels**

A research proposal and executable prototype prepared for Vladimir Reshetnikov,
September 15, 2026. Read `article/forge_delta.pdf` (or build its complete LaTeX
source). The work is an increment relative to the pinned Forge design, not an
installed `forge` tactic or a replacement for its existing controller.

## What is included

The polynomial-machine worker discovers a finite space of observations closed
under coefficientwise pullback along control-flow edges. Its exact certificates
prove zero-valued outputs for every finite rational input word. For updates
affine in state, polynomial in inputs, and bounded-degree outputs, the article
gives a finite-dimensional decision theorem. Retained origins construct concrete
counterexample executions when an initial observation is nonzero.

The second worker proposes and checks finite Kripke countermodels. Its meaning
is nonderivability in the specified intuitionistic propositional **object
calculus**, not the negation of a Lean proposition and not unrestricted Lean
noninhabitation. In particular, it can refute Peirce's formula in IPC while Lean
can prove that formula classically.

## Recorded evidence

- **151 pytest tests passed** (see `results/pytest.txt`).
- **66 machine cases:** 37 closure certificates, 28 execution counterexamples,
  one unknown.
- **16 IPC cases:** 8 countermodels, 8 unknown controls; no positive IPC theorem
  is claimed from bounded model-search exhaustion.
- All **73 certificates replay without site packages**, using `python -S replay.py`.
- Three repetitions per case retained identical certificate contents.
- **222 local Lean identity obligations generated, not compiled.**

The cases are transparent synthetic examples and seeded conjugacy families.
There is **no** head-to-head comparison against `grind`, no real Lean benchmark,
no verified Python checker, and no source-to-Lean semantic reifier. The largest
compact certificate is 915 bytes, excluding its problem and metadata.

## Reproduce

Python 3.11+ is intended; Python 3.13.5 with SymPy 1.14.0 was tested.

```sh
python -m pip install -r requirements.txt
python -m pytest -q
python -S replay.py
python -m forge_delta.experiment --output reproduced-results --repeats 3
python emit_lean.py
```

The experiment refuses to overwrite a nonempty output directory. Stored
mathematical problems/certificates contain no JSON floats. Timing observations
are separate in `results/trials.json` and `results/measurements.csv`.
`results/diagnostics/initial-replay-failure.txt` records an initial packaging
failure and its repair; it is not accepted evidence.

A small Python API example:

```python
from forge_delta.cases import machine_cases
from forge_delta.search import solve
from forge_delta.checker import verify_positive

case = machine_cases()[0]
answer = solve(case["problem"], case["limits"])
assert answer["status"] == "proved"  # restricted machine semantics, not Lean
assert verify_positive(case["problem"], answer["certificate"])
```

Custom problems can be built with `forge_delta.search.machine`, using exact
SymPy rational expressions in `x0, ...` for state and `u0, ...` for payloads.
Use `sympy.Rational(1, 2)` for fractions, not a Python floating-point expression.
Updates are simultaneous. Numerical guards are not supported. See `cases.py`
for finite control, symbolic initialization, two-payload, and false examples.

## Build the article

```sh
cd article
pdflatex -interaction=nonstopmode -halt-on-error forge_delta.tex
pdflatex -interaction=nonstopmode -halt-on-error forge_delta.tex
```

A standard TeX installation with the packages named in the preamble is needed.
No font files or third-party repositories are distributed.

## Lean status

No Lean, Lake, or Elan executable was present. `lean/Reachability.lean` and
`lean/WorkedFold.lean` are uncompiled integration targets. The generated
`lean/GeneratedIdentities.lean` consists of local algebraic proof obligations,
not an original-source semantic bridge. Its `#print axioms` commands are for a
future successful compilation, not evidence that an audit already ran.

Use an existing project with the intended pinned Mathlib and run `lake env lean`
on the absolute paths to these files. The reviewed Forge target was Lean
`v4.34.0` / Mathlib `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`. This archive does
not silently fetch that project or claim version compatibility has been tested.

## Layout

`forge_delta/` contains the producer, independent replay, model finder, case
generators, and experiment driver. `tests/` contains mutation, scope, differential,
and cutoff tests. `results/` contains exact evidence plus observations. `lean/`
contains uncompiled integration targets. `docs/` records the audit, limitations,
and a staged merge plan. `article/` contains the full article and its PDF.

Original source code in this package is provided under the MIT license in
`LICENSE`. Upstream projects retain their own licenses and are not vendored.
