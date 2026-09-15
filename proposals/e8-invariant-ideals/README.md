# Forge extensions: invariant ideals, finite covers, and constructive projection

Read **article/forge-extensions.pdf**. The editable document is
**article/forge-extensions.tex**, with section files in the same directory.

This supplementary package extends the audited Forge design. It does not change
any GitHub repository and does not install a Lean tactic.

## New algorithms

* `invariant_space.py`: greatest constant-multiplier pullback-stable generator space.
* `ideal_space.py`: greatest generator space with bounded polynomial multipliers;
  linear restriction steps avoid a direct bilinear generator/multiplier ansatz.
* `finite_cover.py`: exact finite-algebra induction covers and concrete tree DAGs.
* `presburger.py`: constructive one-output integer projection with CRT, floor/mod,
  a symbolic feasibility guard, and a compact witness program.

The article additionally specifies proof-directed higher-order fold sketches,
including the representation-law issue for Leant's Church-encoded indexing query.
That integration is not implemented or benchmarked here.

## Run

No third-party Python packages are needed. Intended Python minimum: 3.9.
The recorded run used Python 3.13.5.

```sh
cd prototype
python -S -m unittest -v test_prototypes
python -S verify.py
python -S run_experiments.py --output ../reproduced-results
```

The replay driver disables search entry points before checking the corpus.
Reproduction writes a separate directory by default, preserving recorded results.

## Recorded evidence

21 test methods pass. All 422 stored certificates replay: 51 constant-multiplier,
14 polynomial-multiplier, 136 finite-algebra, and 221 integer-projection records.
Some are empty packets or concrete counterexamples, not successful source goals.
The separate integer experiment compares 220 symbolic systems at 3,400 parameter
valuations against a complete concrete enumeration oracle.

These are **Python checks, not Lean kernel proofs**. Shared polynomial arithmetic
and a shared integer-program assembler remain common-mode failure risks. The
mathematical soundness arguments and exact scope of completeness are in the PDF.
The code is research software, not hardened for arbitrary hostile resource use.

## Lean status

`lean/CoreSoundness.lean` and `lean/IndexingSketch.lean` are hand-written specimens,
not generated proof artifacts. They were **not compiled**, because this runtime
has no Lean executable. `lean/status.json` records `NOT_RUN`.

With the pinned Lean toolchain available, run `python lean/check.py`. It records
actual compiler outcomes. A successful run would validate those specimens only,
not the Python checkers or a complete Forge implementation.

No head-to-head benchmark with grind, Aesop, LeanHammer, or another tactic was run.
The original Leant indexing and simultaneous-universe acceptance goals are not
claimed solved.

## Rebuild PDF

```sh
cd article
pdflatex -interaction=nonstopmode -halt-on-error forge-extensions.tex
pdflatex -interaction=nonstopmode -halt-on-error forge-extensions.tex
pdflatex -interaction=nonstopmode -halt-on-error forge-extensions.tex
```

Stock pdfLaTeX packages; no shell escape or bibliography tool required.
`generated-results.tex` holds the counts from the recorded run.

## Provenance and license

See `docs/provenance.json`, `docs/acceptance.md`, and the article's appendices.
The new supplementary material uses MIT-0. No original repository source,
third-party paper, library source, or font file is redistributed.
