# Forge: Three Algorithmic Extensions Beyond the Current Design

The **30-page article** is `article/forge_extensions.pdf`; its editable source
is `article/forge_extensions.tex` with `article/measurements-table.tex`.

This is a research and implementation package for extending Forge's inspected
merged design, not an implemented Lean tactic. The additions are:

1. Inductive-subspace synthesis: find a whole polynomial family satisfying
   `p(T(x)) = H p(x)`, rather than only conserved quantities. The article proves
   termination and bounded-degree completeness for the specified affine model.
2. Hypergeometric antidifference and order-one creative-telescoping search,
   including a separately derived nonsingular boundary treatment of the
   squared-binomial sum. The executable checker proves algebraic identities,
   not the source sequence or universal boundary obligations.
3. Bounded two-sided noncommutative consequence search, with exact word-sensitive
   certificates `f = sum coefficient * left * relation * right`.

The article also specifies an unimplemented fresh-input coefficient-map
extension for polynomial list folds, a universal-assertion backend for exact
Leant/Djex candidates, concrete Lean modules and libraries, and acceptance gates.

## Recorded results

| Family | Stored certificates accepted by independent Python replay |
|---|---:|
| Inductive subspaces | 24 |
| One-variable antidifferences | 15 |
| Bivariate creative telescoping | 1 |
| Noncommutative two-sided relations | 25 |
| **Total** | **65** |

The generated experiment rejected **188 invalid certificate variants**, recorded
**1,100 assertions**, and retained **7 expected UNKNOWN results**. The separate
`unittest` suite passed **13 named test methods**. The same-feature invariant
ablation solved 24/24 with subspace closure and 3/24 with conservation-only
constraints. This selected/planted corpus is a mechanism comparison, not a
representative tactic benchmark and not a run of the original Forge prototype.

The squared-binomial boundary regressions cover 527 `(n,k)` pairs with
`0 <= n <= 30` and `0 <= k <= n+1`, plus sum and flux checks. Finite regressions
are not universal proofs. The mathematical boundary argument is in the article.

## Quick start

The stored-certificate replay requires only Python's standard library:

```sh
python -S prototype/checker.py
```

Search was tested with **Python 3.13.5 and SymPy 1.14.0**. The code requires
Python 3.10 or newer for its syntax and standard-library interfaces, but other
Python versions have not been tested here.

```sh
python -m pip install -r prototype/requirements.txt
python -m unittest discover -s prototype -p 'test_*.py' -v
python prototype/experiments.py --output reproduced-results
python -S prototype/checker.py reproduced-results/problems.json reproduced-results/certificates.json
```

The experiment refuses a nonempty output directory so that the recorded run is
not overwritten. Exact results are deterministic at the tested dependency
version; timings can vary. Timings exclude imports, corpus construction outside
the search call, the ablation, mutations, serialization, and all Lean work.

Generate the two integral Lean noncommutative replay scripts again:

```sh
python prototype/emit_lean.py
```

Generation is not proof checking. See `lean/README.md` for the **unexecuted**
Lean build instructions and `#print axioms` checks. No Lean executable was
available, no Lean kernel result is claimed, no generic verified JSON checker
is implemented, and no stock tactic benchmark was run.

Build the PDF:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error forge_extensions.tex
```

The LaTeX source uses standard TeX Live packages and Latin Modern fonts. Font
files and third-party source trees are not included.

## Evidence and review scope

`results/summary.json`, `measurements.json`, `problems.json`, and
`certificates.json` preserve the main experiment. `mutations.json`,
`unknowns.json`, `assertions.json`, and the logs preserve the controls.
`docs/status.json` separates executed algorithms, uncompiled Lean targets, and
unimplemented adapters. `docs/review-scope.md` lists inspected repository files
and the bounded nonduplication claim.

Pinned repositories:

- Forge: `674521027d968d59f7b83220ed52304a85cb55e2`
- Leant: `6bf05ad78c467989e68290f2d08bbed40802d485`
- Djex: `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`

The Lean target reuses Forge's reported baseline: Lean v4.34.0 and Mathlib
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`. Only the NoncommRing source was
additionally inspected at that exact Mathlib commit; other library compatibility
must be established by a real build. No repository was modified.
