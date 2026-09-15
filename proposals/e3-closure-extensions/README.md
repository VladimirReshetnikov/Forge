# Forge Closure Extensions

**Article:** `article/forge_closure.pdf` (35 pages), with editable source in
`article/forge_closure.tex` and `article/sections/`.

This package develops four concrete certificate-producing algorithms extending
the reviewed Forge design:

- **PRC:** goal-generated polynomial pullback vector-space closure.
- **GI:** goal-generated ideal closure, with reconstructed polynomial multipliers.
- **FRC:** finite-state all-words contracts and shortest distinguishing words.
- **BFT:** first-order binomial-power moment recurrences with boundary-safe flux certificates.

The mathematical foundations are established methods, not claimed new fields.
The contribution is the focused Forge adaptation, executable algorithms,
certificate formats, integration plan, and tests. The report distinguishes the
implemented additions from related ideas already in the repository.

## Evidence and limitations

The recorded run has **317 cases**: 178 positive certificates, 135 concrete
counterexample certificates, and 4 explicit unknown outcomes. All **313 stored
certificates** replay with a standard-library-only checker. All **25 targeted
invalid mutations** are rejected. A separate greatest-fixed-point oracle agrees
with all **240 main finite-state cases**. The 12-method unit suite includes 200
random rational-polynomial cases, each comparing three arithmetic operations.

These counts are different units; they are not combined into a “proof count.”
The experiments begin with mathematical problem data, not original Lean source.

**Lean execution: NOT_RUN. No Lean executable was available.**
`lean/BridgeSpec.lean` is an uncompiled generic proof specimen, not an installed
`forge` tactic. Source-to-IR bridges, Lean polynomial replay, the binomial sum
bridge, and comparisons against existing Lean tactics remain future work.
A Python acceptance is not a Lean-kernel proof.

Review baseline: Forge `674521027d968d59f7b83220ed52304a85cb55e2`.
Review scope and exact source identities are in `audit/review.json`. The review
covered selected merged-design sections and neighboring integration documents,
not an exhaustive line-by-line audit of every frozen proposal.

## Replay with no third-party Python dependency

From `prototype/`:

```sh
python -S -m forge_closure.verify ../results/certificates
```

The command takes a directory or individual JSON files and works without shell
wildcard expansion. The checker imports no SymPy or producer module.
Stored bundles contain both a mathematical problem and its certificate. A real
Lean integration must obtain the problem independently from its source reifier,
not allow the external producer to replace both sides of that contract.

## Reproduce search and tests

Tested environment: Python 3.13.5, SymPy 1.14.0, Linux x86-64.

```sh
cd prototype
python -m pip install -r requirements-search.txt
python run_experiments.py --out reproduced-results
python -m unittest discover -s tests -v
python -S -m forge_closure.verify reproduced-results/certificates
```

The new run writes to a new directory by default, preserving the shipped
`results/` evidence. The fixed seed is 20260915; elapsed times are not expected
to reproduce exactly. Producer timings include their own final Python replay,
but exclude startup/imports, problem generation, JSON I/O, and all Lean costs.

One initial development run exceeded an incorrectly anticipated flux-degree cap.
Its failure is retained in `results/initial-cap-failure.txt`. The low-cap case
is now an expected unknown control; the acceptance checks were not weakened.

## Try a custom polynomial problem

From `prototype/`, in a Python session:

```python
import sympy as sp
from forge_closure.search import make_problem, ideal_search
from forge_closure.checker import verify

x, y = sp.symbols("x y")
problem = make_problem(
    (x, y),
    transitions=[(x*x, y*y)],
    initial=(2, 2),
    targets=[x-y],
)
result = ideal_search(problem)
assert result["status"] == "proved"
assert verify(problem, result["certificate"])
print(result)
```

The certificate is based on `x*x-y*y = (x+y)*(x-y)`. The vector-space worker on
the same problem reaches its default degree ceiling, illustrating why the ideal
worker is a distinct capability rather than a larger vector-search budget.

## Build the article

With pdfLaTeX and standard LaTeX packages available:

```sh
python build_article.py
```

The script runs three passes, without shell escape. The PDF was rendered and
visually inspected. The archive contains no font files, copied papers, or
upstream checkout. No remote repository was modified.

## Operational caution

These are research producers and a research checker. Degree, term, basis,
coefficient-size, relation-size, and input-byte limits exist, but the code is not
hardened against arbitrary hostile resource exhaustion. Some SymPy calls are
synchronous and require an external process timeout in production. A resource
failure is not a proof that the original theorem is false.
