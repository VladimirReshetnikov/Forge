# Forge: A Certificate-Driven Proof Planner Beyond Lean's grind

This research artifact proposes a substantially broader Lean tactic by combining
proof-structure discovery with existing local reasoning engines. Read
`article/forge.pdf` for the complete article; `article/forge.tex` is its source.

## What is implemented—and what is not

**Implemented and executed:** small Python prototypes of demand-directed Horn
reasoning, accumulator-lemma synthesis with explicit list induction, exact
rational nonnegativity certificates, Bernstein subdivision certificates, and
polynomial witness synthesis. The recorded test run passed **69 tests**. A
separate standard-library-only command replayed **13 persisted certificate
bundles**.

**Not implemented:** an end-to-end `forge` Lean tactic, a Lean formalization of
the Python checkers, the complete proposed planner, a generic induction
synthesizer, or a comparative Lean benchmark. The two `.lean` files are ordinary
reference proof scripts, **not compiled here** because no Lean executable was
available. Python verification is not Lean-kernel verification.

The Horn measurements compare two deliberately small implemented search
policies; neither is an implementation or emulation of `grind`. No measured
speedup or success-rate improvement over Lean's current tactics is claimed.

## Read first

- `article/forge.pdf`: 31-page article, mathematical derivations, source audit,
  concrete algorithms, architecture, implementation roadmap, and evaluation plan.
- `results/results.json`: raw measurements and environment versions.
- `results/certificates.json`: portable exact certificates used by the replay
  command, including the original assumptions and goals.
- `sources.json`: original-source URLs, bibliographic descriptions, and snapshot
  status. No third-party source code or fonts are bundled.

## Reproduce the Python experiments

Python 3.13.5 was used. The source uses Python 3.10+ syntax; only the recorded
3.13.5 environment has been exercised. Dependency versions are recorded in
`requirements.txt`; those exact versions might require a newer Python than 3.10.
Run from the archive's root directory:

```sh
python -m venv .venv
# Linux/macOS:
. .venv/bin/activate
# Windows PowerShell instead:
# .venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
python -m pytest -q
python scripts/run_experiments.py
python -S scripts/verify_certificates.py
```

The experiment command overwrites the generated measurement and certificate
files in `results/`. Timings are single-machine illustrative measurements and
will vary. Search outcomes can also change with numerical-solver versions;
**no numerical search result is accepted without exact rational replay**.

To verify the saved bundles without installing NumPy, SciPy, SymPy, or pytest:

```sh
python -S scripts/verify_certificates.py
```

The `-S` flag disables loading site packages. Verification uses the included
Python checker modules and the standard library. It is separate from search,
although search and checking share representations and exact polynomial
operations. The checkers are not formally verified and are not a hardened
untrusted-input service.

## The experiments

| Mechanism | Recorded outcome |
|---|---|
| Accumulator-lemma discovery | Candidate 41 yields `revAcc(xs, acc) = app(rev(xs), acc)`; 49 finite sample contexts prune the grammar; explicit induction, not sampling, validates the result. |
| Horn demand search | At depth 12, the forward policy generates 4,096 facts while backward search produces a 13-node proof. At depth 16, forward search reaches its 5,000-node cap; backward search produces a 17-node proof. |
| Nonnegativity search | Five named polynomial targets obtain exact certificates; the quartic example uses 280 candidate columns, 35 coefficient equations, and a three-term certificate. |
| Negative search control | The true square `(x+y+1)^2` has no certificate in the restricted searched dictionary, although a manually supplied one-square certificate checks. |
| Bernstein subdivision | `x^2-x+3/10` on `[0,1]` is certified using two leaves after the initial coefficient test fails. Each leaf has lower bound `1/20`. |
| Witness synthesis | Candidate 23 is `x^2+1`, with exact certificates for `w-x >= 0` and `w+x >= 0`. |

There are 13 top-level saved bundles: one list-theorem bank, four Horn proofs,
six polynomial certificates (including the manually supplied search control),
one subdivision proof, and one witness with its two side-condition proofs.
A cone certificate is **conditional on its stated guards**. The checker does
not establish those guards. A Horn certificate similarly assumes its listed
facts and rules. Their Lean realization must bind every such assumption to the
actual local context.

## Source layout

```
article/                 LaTeX article and PDF
forge_lab/poly.py        Exact sparse rational arithmetic and cone/box checking
forge_lab/nonlinear.py   Untrusted numerical LP search and exact box search
forge_lab/terms.py       Typed first-order terms and rewrite-trace replay
forge_lab/induction.py   List-induction checking and bounded lemma synthesis
forge_lab/horn.py        Forward/backward Horn search and proof-DAG replay
forge_lab/witness.py     Bounded polynomial witness enumeration
scripts/                 Experiment, replay, and optional Lean-check commands
tests/                   Differential, positive, negative, and mutation tests
results/                 Recorded logs, raw data, and saved certificates
lean/                    Uncompiled ordinary Lean reference scripts
sources.json             Bibliography and version/snapshot inventory
requirements.txt         Executed Python dependency versions
build_article.sh         XeLaTeX build helper
```

## Lean reference scripts

`lean/Structural.lean` uses `import Lean` and defines its own elementary list
operations. With a Lean executable on PATH:

```sh
python scripts/check_lean.py
```

This updates `results/lean_status.json` with the **actual** outcome, or `NOT_RUN`
when Lean is absent. It does not install Lean or run a `grind` benchmark.

`lean/CertificateExamples.lean` needs a compatible Mathlib project:

```sh
# From that project's root, replacing the example path:
lake env lean /absolute/path/to/forge_grind/lean/CertificateExamples.lean
```

This is a suggested compilation command, not a claim that it was executed.
The source audit pins Lean core to v4.34.0, but the external libraries discussed
in the article do **not** have a verified common dependency manifest here.
Their compatibility must be established before integration. In particular, an
observed SOS toolchain snapshot targets v4.32.0-rc1.

## Build the article

Install XeLaTeX and the packages used in `article/forge.tex`, together with the
**Noto Serif**, **Noto Sans**, and **DejaVu Sans Mono** fonts. No font binaries are
included. Then run:

```sh
sh build_article.sh
```

The helper runs XeLaTeX three times for references and the table of contents.
The bibliography is embedded in the `.tex`; BibTeX is not required. You can
change the three `fontspec` declarations to locally available fonts.

## Interpretation

The main design contribution is a shared, scope-aware proof-obligation planner
that makes structural synthesis, witness search, theorem instantiation, and
existing nonlinear reasoning cooperate. It is not a claim to have invented
sum-of-squares certificates, equality saturation, SMT proof reconstruction,
lemma synthesis, or AND/OR tactic search. The article identifies existing Lean
libraries and research explicitly, including the current `leanprover/sos`
implementation and QuerySMT.

All prototype failures mean failure of a bounded search or rejection of a
certificate—not that the requested theorem is false. Completion of the proposed
Lean tactic must require a closed proof of the exact original goal, no remaining
metavariables or `sorryAx`, explicit guard discharge, and a declared axiom/trust
policy. Native evaluation and kernel-reduced checking are treated separately.
