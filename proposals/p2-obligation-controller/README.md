# Forge: beyond grind with structural search and exact certificates

Prepared for Vladimir Reshetnikov, September 14, 2026.

Start with **article/forge.pdf**. Its complete LuaLaTeX sources are alongside it.
The article specifies a proposed Lean tactic; `Forge` is the design's name, not
an existing released package or an implemented end-to-end tactic.

## The design

Retain `grind` for local reasoning. Add a proof-producing controller that can
change the proof obligation: generalize a changing accumulator, select an
induction motive, discover an auxiliary lemma, synthesize a source-level
witness, request a constrained theorem instance, or obtain an exact nonlinear
certificate. Separate proved facts from candidate lemmas and exploratory models.

The article contains concrete algorithms, certificate identities and soundness
arguments, typed-state and Lean integration contracts, library choices,
implementation stages, adversarial failure cases, and a controlled benchmark
plan. It distinguishes existing functionality from proposed additions.

## Executed evidence

| Certificate family | Generated and replayed |
|---|---:|
| List induction and accumulator generalization | 6 |
| Polynomial additive recurrences | 65 |
| Affine witnesses and Farkas certificates | 63 |
| Finite-dictionary square certificates | 40 |
| Bernstein subdivision certificates | 41 |
| **Total** | **215** |

All **31 unittest methods pass**. Each may contain several regression trials.
All **215 certificates replay with Python's standard library alone**.

Notable ablations: the original fixed-accumulator induction search stalls, but
an automatically generalized statement succeeds; a constant witness template
fails on an unbounded strip while an affine witness succeeds; root-only
Bernstein checking certifies 25 of 41 designed positive cases and subdivision
certifies all 41. See the article for the exact conditions and negative cases.

These are designed Python micro-experiments, not a representative Lean corpus.
In particular, the 40 square-certificate cases are generated from the same
finite dictionary searched by the solver. No Lean executable was available;
no Lean/grind head-to-head comparison, Lean compilation, or kernel replay
was performed. `lean/ReplayExamples.lean` is explicitly uncompiled and is not
counted among the passing tests. The exact Python checkers are not formally
verified; search and replay share some representation code.

## Reproduce the experiments

The recorded environment is Python 3.13.5, NumPy 2.3.5, and SciPy 1.17.0.
Use a virtual environment and run from `prototype/`:

```sh
python -m pip install -r requirements.txt
python -m unittest discover -s tests -v
python run_experiments.py --output ../reproduced-results
python -S replay_certificates.py ../reproduced-results/certificates
```

Replay the supplied certificates without installing NumPy or SciPy:

```sh
cd prototype
python -S replay_certificates.py ../results/certificates
```

The search code uses SciPy/HiGHS only to propose LP solutions. Acceptance uses
exact rational coefficient identities and signs, never numerical tolerances.
A rejected proposal or exhausted search budget means **no certificate found**,
not a proof that the mathematical statement is false.

Timings may change between machines/runs. Seeds, environment, counts, individual
certificates, and raw logs for the supplied run are in `results/`.

## Build the PDF

Install a TeX distribution with LuaLaTeX and the packages named in
`article/forge.tex`. The font selections are Linux Libertine O, Lato, and DejaVu
Sans Mono. No font files are distributed in this archive. Substitute available
fonts in the three `fontspec` declarations when necessary.

From `article/`:

```sh
lualatex -interaction=nonstopmode -halt-on-error forge.tex
lualatex -interaction=nonstopmode -halt-on-error forge.tex
```

Repeat once if cross-reference warnings remain. The supplied PDF includes
clickable contents, references, and bookmarks.

## Contents

- `article/`: complete article sources and rendered PDF.
- `prototype/forge_proto/`: exact polynomial substrate and five algorithmic workers.
- `prototype/tests/`: reproducible unit/regression tests.
- `prototype/run_experiments.py`: seeded searches and certificate generation.
- `prototype/replay_certificates.py`: search-free exact replay.
- `results/`: recorded results, logs, and every accepted certificate.
- `lean/ReplayExamples.lean`: uncompiled proof-shaped Lean illustrations.
- `SOURCES.md`: source ledger and version/compatibility boundaries.

## Suggested implementation order

Build the typed controller and local-solver adapter first. Then port accumulator
generalization and structural-induction replay, followed by recurrence and
affine-witness certificate reconstruction. Integrate the existing Lean SOS
library for the production nonlinear worker. Only then add persistent native
grind-state integration, general quantifier search, and higher-order/external
ATP workers. Each stage has separate exit criteria in the article.
