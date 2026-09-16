# Order matters: noncommutative certificates for Forge

A research extension prepared for Vladimir Reshetnikov, 15 September 2026.

Start with **[the PDF article](article/forge-noncommutative.pdf)**. The main
source is [article/forge-noncommutative.tex](article/forge-noncommutative.tex).
The article is split into section files; compile from the `article` directory.

## Implemented

The standard-library Python reference implementation provides two-sided ideal
certificate search; exact incidence-component slicing; complete, uncapped
homogeneous-relation reasoning with truncated-quotient matrix countermodels;
unique homogeneous word Gram matrices and exact LDL square factors; bounded
positive-ray search modulo equality spans; structural involution/commutation
ray proposals; and trace receipts with explicit commutator residuals.

The checker is separately implemented. It imports neither the search arithmetic
nor its elimination code. The standalone replay actively blocks those imports.
The object language has **rational central coefficients and ordered words**.
Operator and trace interpretations are different and cannot be relabeled.

## Recorded evidence

Python 3.13.5; seed 2026091503; all commands below ran with `-S`.

- 90 equality queries against three independent exact oracles: 45 identities and
  45 whole-matrix countermodels, with no oracle disagreement.
- 40 homogeneous Gram queries: 20 square receipts and 20 nonreceipt outcomes,
  with no disagreement against an independent all-principal-minors oracle.
- 9 worked receipts, including a CHSH operator bound and a separate
  self-adjointness identity. The CHSH ray dictionary is generated from relations.
- 119 stored evidence objects replayed independently; 57 unittest methods pass
  (including a method with 24 atom-permutation subtests); 195 falsifying mutations
  rejected. These counts measure different things and are not one pass rate.

See `results/experiments.json`, `results/replay.json`, `results/unit-tests.log`,
and `results/mutations.json` for the actual run. Timings are single observations,
not Lean timings or general speedup estimates.

## Run locally

No third-party Python dependencies or network calls are used. Tested on Python
3.13.5; the source uses Python 3.10+ syntax.

```sh
cd prototype
python -S -m unittest discover -s tests -v
python -S replay.py ../results/certificates.json
python -S experiments.py --output ../reproduced-results
python -S mutation_audit.py
```

The experiment command writes separately from recorded results. The mutation
command reads the recorded corpus and regenerates `results/mutations.json`.
To explore individual algorithms, use the direct API example near the end of
the article or the fully worked `examples()` function in `experiments.py`.

`BudgetExceeded` is an explicit producer resource failure. A host must map it to
UNKNOWN, not to a false theorem. `None` from a positivity producer is not an
operator countermodel. The checker result is evidence about the precise object
problem; it has no authority to assign a Lean metavariable.

## Lean status — NOT_RUN

No Lean or Lake executable was available. This is **not an installed Forge
plugin**, and there is no source reifier or formally verified computational
checker. The six targets in `lean/CertificatePrinciples.lean` are supplied as
uncompiled reconstruction targets, with no `sorry` or introduced axioms.

In an existing, already built compatible Mathlib project, the explicit gate is:

```sh
python tools/check_lean.py --project /path/to/mathlib-project
```

Missing tools return exit code 2 and NOT_RUN. Even successful elaboration of
those six targets would not validate the absent reifier or all JSON receipts.
No comparison with `grind`, `noncomm_ring`, or Forge was executed.

## Build the article

```sh
tools/build_article.sh
```

This needs pdfLaTeX and standard TeX packages. The script runs three passes.
No font binaries or third-party software are bundled.

## Scope and provenance

The main baseline is Forge `c98e47c5f804e92880fc1d0e378c1b95832b685c`.
Leant and Djex read snapshots and review scope are in `docs/source-audit.md`.
No remote repository was modified. See `docs/schema.md`, `docs/limitations.md`,
and `docs/initial-failure.md` before treating the prototypes as an integration.
The mathematical methods are not claimed to be newly invented; their proposed
capability composition and executable contracts are the extension to Forge.
