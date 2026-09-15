# Forge: Finite Certificates for Infinite Behaviors

A 29-page research article and executable prototype package for three extensions
to Vladimir Reshetnikov's Forge design. Prepared 15 September 2026.

Start with **article/forge_extensions.pdf**. Its complete editable LaTeX source
is in **article/**, with `forge_extensions.tex` as the entry point.

## What is new in this package

**Observable-space closure.** Starting from a target observation, construct the
smallest action-invariant row space needed to decide it. The finite rational
linear fragment returns either a matrix certificate valid for every finite input
word or a concrete distinguishing word. No conservation law has to be guessed.

**Target-generated polynomial ideals.** Repeatedly pull the target and its
auxiliary generators back through the updates, closing their ideal. Export
polynomial multiplier identities rather than trusting a Gröbner-basis result.
The article proves termination and completeness for the precisely stated,
unguarded total polynomial fragment, with polynomial initial parameterizations
over the rationals. The prototype imposes explicit budgets and reports unknown
when they are exhausted. This is not a general reachability decision procedure.

**Pole-free binomial summation.** Search by exact linear algebra for a recurrence
and a polynomial telescoping certificate in an endpoint-safe binomial basis.
The implementation produces seven binomial-moment recurrences. Singular leading
coefficients are handled as a separate recurrence-comparison obligation, not
silently divided away. A recurrence certificate is not a closed-form theorem.

The article also specifies source-compilation obligations, concrete Lean/Mathlib
modules, a restricted universal-behavior verifier for Leant, certified semantic
pruning requirements, an affine monomial-lift adapter, and implementation gates.
The last three are designs, not additional executed workers.

## Recorded evidence

| Worker | Input cases | Certificates | Concrete counterexamples | Bounded unknowns |
|---|---:|---:|---:|---:|
| Observable closure | 36 | 22 | 14 | 0 |
| Polynomial ideal closure | 13 | 9 | 3 | 1 |
| Binomial summation | 10 | 7 | 0 | 3 |
| Total in this package only | 59 | 38 | 17 | 4 |

- All 55 positive/negative bundles replay with Python site packages disabled.
- All 818 single-entry coefficient mutations are rejected.
- All 117 regression test items pass. Test items, mutation trials, numerical
  observations, and input cases are distinct units.
- Search timings are one-shot measurements; checker timings are medians of five
  warm calls. Import, process startup, and Lean costs are excluded.
- Development failures and corrections remain recorded separately in `results/`.

**These are Python results, not Lean-kernel proofs.** No Lean executable was
available, so the Lean sources are uncompiled specimens. This package does not
install a `forge` tactic, does not include a verified Lean reifier or reflected
checker, and does not claim a speedup or solved-goal gain against `grind` or any
other tactic. Python validation is not a security guarantee or a formal proof of
the checker implementation. Search inputs are intended as research workloads.

## Run the checkers without dependencies

From this directory:

```sh
python -S prototype/checkers.py results/certificates results/counterexamples
```

The expected report has `checked: 55`, an empty `failed` array, and
`site_packages_enabled: false`. The checker is separately implemented using only
the standard library. It does not import the search module or SymPy.

## Reproduce the experiments and tests

Python 3.10 or newer is required by the code syntax. The recorded run used
Python 3.13.5 and SymPy 1.14.0. A separate environment is recommended:

```sh
python -m venv .venv
# Activate the environment using the command appropriate to your shell.
python -m pip install -r requirements.txt
python -m prototype.run_experiments --output reproduced-results
python -S prototype/checkers.py reproduced-results/certificates reproduced-results/counterexamples
python -m pytest -q
```

The default experiment output is `reproduced-results/`, so rerunning does not
replace the recorded corpus. Tests replay the retained `results/` corpus. The
expected exact identities and outcome categories are deterministic; timings
are machine-dependent. This is a constructed experimental corpus, not a sample
of arbitrary Lean goals.

For a small executable example using `ideal_problem`, `ideal_search`, and the
independent `verify(problem, certificate)` call, see Appendix A of the article.

## Rebuild the article

Install a LaTeX distribution providing pdfLaTeX and the ordinary packages used
by the source, then run:

```sh
python build.py
```

The build uses a temporary directory for compiler intermediates, runs three
passes, and updates `article/forge_extensions.pdf` and `results/latex-build.log`.
It does not need shell escape or a bibliography processor. No font files are
included. `metrics.tex` and `recurrences.tex` record the saved experimental run;
a new local timing run does not automatically change the article's tables.

## Lean specimens

`lean/` is a separate specimen project pinned to Lean v4.34.0 and the Mathlib
revision used by the audited Forge design. Its generic execution-invariant glue
and hand-written nonlinear/summation replay targets contain no `sorry`, but
**have not been compiled or axiom-audited**. On a machine with the pinned
toolchain and fetched Mathlib dependencies, `lake build` is the first validation
gate. The article describes the additional bridges needed before these workers
can close actual Lean goals.

## Archive map

- `article/`: PDF, main TeX, section sources, bibliography, and generated tables.
- `prototype/`: searches, independent exact checkers, and corpus runner.
- `tests/`: regression, schema, boundary, and differential tests.
- `results/`: 38 certificates, 17 counterexamples, 59 input problems, measurements,
  mutation records, successful test logs, and separated failed-development logs.
- `docs/`: incremental-contribution audit, validation ledger, and source manifest.
- `lean/`: uncompiled Lean project and replay specimens.

The audit is scoped to the inspected merged Forge design, its status/provenance
ledgers, and the explicitly listed neighboring sources. It is not a byte-for-byte
audit of every historical proposal. Existing proof planning, trust policies,
induction generalization, arithmetic witnesses, and certificate orchestration
are treated as prerequisites rather than claimed as new ideas. Mathematical
antecedents are cited in the article; no claim of mathematical priority is made.

Original package material is provided under MIT-0; see `LICENSE`. Referenced
projects and publications retain their respective terms. No third-party source
or publication PDF is redistributed in this archive.
