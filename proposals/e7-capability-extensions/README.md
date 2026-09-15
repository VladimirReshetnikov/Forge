# Forge: capability extensions

**Start with [`article/forge-extensions.pdf`](article/forge-extensions.pdf).**

Prepared for Vladimir Reshetnikov, 15 September 2026. This is an additive research
package, not a replacement for Forge's existing article and not an installed
Lean tactic. It contains original prototype code and an editable LaTeX article.
No repository was modified.

## The additions

1. **Continuation-local synthesis:** derive local base and step contracts from a
   fold specification; search the component grammars before composing them;
   retain compatibility constraints rather than blindly multiplying projections.
   The executed fragment constructs a typed finite-list indexing algebra.
2. **Inductive algebra:** compute a greatest pullback-stable polynomial vector
   space, or close a target-generated ideal under pullback. The former has a
   degree-bounded affine-fragment completeness theorem; the latter handles
   polynomial multipliers and can return exact orbit counterexamples.
3. **Cyclic proof compilation:** discover phase-sensitive affine or lexicographic
   descent for a supplied recursive call graph, with exact inequality witnesses.
   A proposed Lean bridge closes such calls by ordinary well-founded induction;
   it does not accept circular proof terms.

The article explains the source-relative delta, mathematical claims and proofs,
algorithms, worked examples, failure modes, certificate formats, concrete
libraries, proposed module boundaries, and integration acceptance gates.

## Run the portable tests and experiments

From this directory:

```sh
python -S -m unittest discover -s prototype -p 'test_*.py' -v
python -S prototype/run_experiments.py --out reproduced-results
python -S prototype/replay.py reproduced-results/certificates.json
```

The main code uses only the Python standard library. The recorded run used
Python 3.13.5; Python 3.10 or newer is recommended for the syntax used here.
Other Python versions were not tested. `-S` disables normal site initialization.

Replay the archived run without repeating the search:

```sh
python -S prototype/replay.py results/certificates.json
```

Optional differential validation, separate from the acceptance boundary:

```sh
python -m pip install sympy==1.14.0
python prototype/validate_sympy.py --out reproduced-results/sympy-validation.json
```

The scripts default to `reproduced-results/` rather than overwriting the original
`results/`. All timings are observations on small synthetic fixtures, not
comparisons against Lean, grind, Djex, or Leant.

## Recorded results

- 72 affine systems: backward-space and independent forward-feature computations
  agree; 24 have nonzero relation spaces.
- 40 constructed nonlinear systems: target and action identities verified.
- 14 positive ideal-completion fixtures; three independently executed orbit
  counterexamples, including a noncommuting-transition ordering control.
- Four valid ranking certificates; two invalid cyclic examples remain unknown.
- Largest synthesis fixture: 50,940 flat complete candidates versus 61 local
  component checks and one assembled candidate. These are different work units,
  from a fixed deliberately unfavorable ordering; no production speedup follows.
- 3,570 direct-reference indexing behavior checks, plus symbolic algebra replay.
- 135 encoded certificate records replayed; 31 corruptions rejected.
- 29 portable regression test methods passed.
- Optional SymPy differential test: 368 remainders agree over 32 systems;
  185 traced basis identities also pass independent exact replay.

These quantities overlap. Do not add them into a combined benchmark score.
The 135 records include three counterexamples and some zero-space controls;
they are not 135 Lean theorems.

## Lean status

**NOT COMPILED.** This environment had no Lean executable. `lean/Specimens.lean`
contains proposed ordinary induction and well-founded-induction lemmas, not an
implementation of `forge`. It includes axiom-printing commands, but no compiler
or axiom-audit receipt is claimed. The source-to-Lean bridges remain proposals.
The package does not resolve Leant's original indexing or two-universe queries.

This status is independent of Forge's already recorded elaboration of three of
its own core design files. See `docs/STATUS.md` and `docs/SOURCE-AUDIT.md`.

## Rebuild the PDF

Install a TeX distribution providing the packages listed in `article/main.tex`,
including newtx, microtype, tcolorbox, and hyperref. Then run:

```sh
python build_article.py
```

The script invokes pdfLaTeX three times and copies the result to
`article/forge-extensions.pdf`. No font files or third-party papers are included.

## Layout

```text
article/        final PDF, main.tex, eight section sources, bibliography
prototype/      exact search algorithms, separate replay, tests, experiment drivers
results/        original experiment outputs and serialized inputs/certificates
lean/           explicitly uncompiled proof specimens
docs/           status, source audit, pinned revisions, integration gates
build_article.py  portable pdfLaTeX build driver
```

`prototype/replay.py` imports none of the search modules and has its own sparse
polynomial implementation. It remains a Python research checker, not a formally
verified or hardened hostile-input verifier. A final Lean implementation must
prove source reification and lower certificates to checked Lean proofs.

## Terms

Original code and article source in this package are released under MIT-0; see
`LICENSE`. Cited projects and publications retain their own terms. This package
does not redistribute their sources, PDFs, binaries, or fonts.
