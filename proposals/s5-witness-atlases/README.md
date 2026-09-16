# Algebraic Witness Atlases for Forge

**Read the article:** `article/atlas.pdf` (source: `article/atlas.tex`).

A concrete research extension to the Forge design reviewed at commit
`58ea206bd7ad501b930add568151217bcc7f82a2`: exact bivariate real quantification,
free-parameter regions, and piecewise root-index witnesses/counterstrategies.

This is a **working Python research prototype**, not an installed Lean tactic.
The Python checker and geometric soundness theorem have **not** been formalized
or checked in Lean. `lean/AtlasQuantifiers.lean` contains only two explicitly
uncompiled semantic composition specimens. No user repository was modified.

## Supported input

Boolean combinations of rational polynomial sign tests in two real variables:

```
Qx x . Qy y . F(x,y)
Qx = forall | exists | free
Qy = forall | exists
```

`F` may use `=`, `!=`, `<`, `<=`, `>`, `>=`, conjunction, disjunction,
negation, and implication. There is one quantifier per variable, in the stated
order. No additional symbolic parameters, transcendental functions, arbitrary
quantified subformulas, integer quantifiers, or variable denominators are parsed.

The baseline uses complete sign-invariant plane atlases. Projection guards are
justified by exact derivative/pair Bézout identities. Exceptional parameter
fibres are recomputed exactly over a localized real algebraic coefficient field.
The checker does not assume the projection polynomial is irreducible.

## Run an example

Python 3.10+ is required; tested with Python 3.13.5. From `prototype/`:

```sh
python -m pip install -r ../requirements.txt
python -m atlas solve ../examples/surjective_cubic/problem.json --output cubic.json
python -S -m atlas verify ../examples/surjective_cubic/problem.json cubic.json
```

`solve` uses SymPy. `verify` needs only the Python standard library. With `-S`,
site packages are disabled. An accepted certificate may prove the encoded
sentence **false**; successful replay and mathematical truth are different
fields. `closed_value: null` means the outer variable is free, not that a
closed sentence has an unknown truth value.

The wire format is documented in the article. Each polynomial is a sorted list
of `[xExponent, yExponent, "rational"]` terms. Rational strings are canonical;
JSON floats are not accepted as exact coefficients.

## Reproduce the tests

From `prototype/`:

```sh
python run_examples.py
python -S verify_corpus.py
python differential.py
python mutation_tests.py
python metamorphic.py
python -S verify_corpus.py ../metamorphic-corpus
python strategy_probes.py
python -m pytest -q
```

Alternatively, run `python run_all.py` from the archive root. It executes the
same commands, captures separate logs, and stops on any nonzero exit code.
Re-running experiments replaces some result files; save the supplied results
elsewhere first to retain the delivered observations exactly. The complete
`run_all.py` entrypoint was also rerun successfully in a separate fresh directory;
see `results/package-reproduction.json`.

### Recorded evidence (do not pool these into one theorem count)

| Experiment | Observed result |
|---|---|
| 24 primary problems | All certificates replay; 19 expected closed verdicts match, 5 exact parameter regions separately checked |
| 76 affine-transformed closed problems | All expected verdicts match |
| 540 targeted corruptions | All rejected |
| 42 unit/regression tests | All pass, including the primary replay cases |
| 250 rational polynomial root problems | Exact agreement with SymPy |
| 200 localized algebraic trials | 194 exact sign agreements, 6 zero denominators rejected |
| 336 independent rational fibre queries | All agree; no oracle-unknown results |
| 25 base cells of five free-variable examples | Match independent exact region formulas |
| 237 transported selector-cell probes | Required witness/counterexample truth holds |
| `python -S` replay | All 100 saved atlases accepted; no SymPy imported |

The initial differential failure is preserved in
`results/differential-initial-failure.log`. An empty sparse polynomial had been
converted to Python integer zero rather than SymPy zero; the conversion was
repaired and the full suite rerun. See `docs/RUN_HISTORY.md`.

## Package layout

- `article/`: modular LaTeX and final PDF; mathematical arguments, algorithm,
  worked examples, schema, integration plan, references.
- `prototype/atlas/`: producer, exact arithmetic, replay checker, JSON loader,
  fixtures, CLI.
- `prototype/tests/` and standalone runners: reproducible verification experiments.
- `examples/`: 24 problem/certificate/strategy triples.
- `metamorphic-corpus/`: 76 transformed problem/certificate pairs.
- `results/`: raw records, logs, environment, replay status, and PDF quality check.
- `lean/`: two uncompiled composition lemmas; no reflected arithmetic checker.
- `docs/`: review scope, implementation status, and observed repairs.

## Build the article

A normal TeX Live or MiKTeX installation with `latexmk`, pdfLaTeX, Latin Modern,
and the AMS, TikZ, stmaryrd, xurl, and other packages loaded by `atlas.tex`
is sufficient:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error atlas.tex
```

No external font files, external paper PDFs, or network downloads are required.
The current article does not need shell escape. `build.ps1` offers the same
command for PowerShell users; `Makefile` provides a Unix convenience target.

## Scope of confidence

The mathematical procedure is complete for the specified fragment without
resource caps. The implementation is finite-resource research code, not a
formal proof or a hardened service. Producer/checker separation does not imply
independent arithmetic: exceptional-fibre operations share `atlas/exact.py`.
Differential and mutation tests are evidence, not a substitute for formalization.

The full root-index function language is specified mathematically and serialized
as selector descriptors; the prototype does not elaborate it into an executable
Lean real-valued function. The article gives the missing Lean proof obligations
and distinguishes noncomputable mathematical witnesses from numerical programs.

Polarity-directed certificate slicing and Boolean-implicant-guided local
projection are **designs only**, not measured features. No speedup over `grind`,
`nlinarith`, Forge's existing workers, or an industrial CAD solver is claimed.
