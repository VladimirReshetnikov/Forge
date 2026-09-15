# Forge: structural search and certified theory cooperation beyond `grind`

**Article:** `article/forge.pdf` (32 pages) and self-contained LaTeX source
`article/forge.tex`. Research/source snapshot: 14 September 2026.

## What this package is

A concrete design for a significantly broader Lean automation system, together
with executed prototypes of its central algorithms. It preserves `grind` as a
strong foundation and adds induction-motive planning, proved auxiliary lemmas,
exact nonlinear certificates, Boolean/theory clause learning, and witness synthesis.

**Not a completed Lean tactic.** No Lean executable was present in the authoring
container, and no Lean code was compiled. `lean/ReplayExamples.lean` is explicitly
uncompiled prospective reconstruction code. `scripts/run_lean_bench.py` is a next-step
harness, not evidence of a head-to-head comparison. There is no installed `forge`
command in this archive. The article distinguishes mathematical soundness arguments,
Python checker tests, proposed Lean reconstruction, and unmeasured performance.

## Executed results

The final unit test log records **64 passed**. The deterministic experiment run
contains 1,494 rows and **1,238 saved successful proof/model bundles**, all replayed
by checking modules that do not import numerical or symbolic search libraries.

| Family | Observed result |
|---|---|
| Sparse cone / equality-ideal certificates | 47 successes out of 49; two deliberate unknowns |
| Exact rational nonnegative quadratics | 40/40 manufactured examples |
| Bernstein covering certificates | 12/13; non-dyadic zero case remains unknown |
| Structural equations | Three synthesized/proved lemmas, two rejected false candidates, two further proved targets |
| Induction ablation | Only generalization **and** proved lemmas together close accumulator reversal |
| Random CNF + integer difference logic | 300 oracle agreements: 189 UNSAT, 111 SAT |
| Pigeonhole CNF | Five replayed UNSAT proofs |
| Residue witness parameters | 831 checked tables; 249 impossible cases by gcd divisibility |

Do not combine these heterogeneous families into a general theorem-proving accuracy
score. Manufactured examples favor their generating certificate grammar. Python
replay is not Lean kernel verification. The recorded timing is one in-process pass,
not a repeated performance study; search timings include internal acceptance checks.
`certificate_bytes` counts a serialized statement plus its certificate, not only a
proof payload.

## Reproduce

Tested interpreter: Python 3.13.5. For all producers and tests:

```sh
python -m pip install -r requirements.txt
python -m pytest -q
python scripts/run_experiments.py
python scripts/verify_artifacts.py
```

To replay the saved successful artifacts **without installing any dependencies**:

```sh
python scripts/verify_artifacts.py
```

Expected final replay message:

```text
1238 saved artifacts replayed successfully using standard-library-only checkers.
This is object-level/exact Python replay, not Lean kernel verification.
```

The independent checker validates the problem statement recorded in JSON. A future
Lean adapter must prove its correspondence to the actual Lean expression and local
hypotheses. The finite witness table's universal interpretation is justified by the
quotient/remainder theorem in the article; sampled integers alone are not a proof.

## Build the article

```sh
make pdf
```

Requires XeLaTeX, latexmk, and the TeX packages referenced in `forge.tex`. Fonts used:
Linux Libertine O, Lato, DejaVu Sans Mono, and Libertinus Math. Fonts are not bundled.
A suitable TeX Live installation plus those installed fonts is sufficient; the four
font declarations at the top of the source can be changed to available equivalents.
No shell-escape, BibTeX, downloaded images, or external bibliography files are needed.

## Lean next-step commands (NOT run here)

In an existing compatible, built Mathlib project:

```sh
lake env lean /path/to/forge-research/lean/ReplayExamples.lean
python /path/to/forge-research/scripts/run_lean_bench.py \
  --project /path/to/existing/mathlib-project \
  --timeout 30 --heartbeats 1000000 \
  --output /path/to/results/lean-benchmark.json
```

The harness preflights imports and records setup failure separately. Additional
actually installed tactics can be passed with `--strategy NAME=TACTIC` and their
modules with `--import-module MODULE`. It records source, stdout, stderr, Lean version,
exit status and fresh-process timing. An `accepted` result means successful Lean
elaboration, not automatic approval of every printed axiom; apply the article's
axiom audit before making assurance claims. No download/build of missing Lean
packages is attempted by the harness.

## Source layout

`prototype/forge_cert/poly.py` is the independent exact rational polynomial checker.
`polynomial_search.py` contains the untrusted SymPy/SciPy-based producers.
`induction.py` contains the small typed object logic, producer, explicit trace replay,
and dependency-checked lemma bundles. `cdclt.py` contains CDCL(T), independent proof
replay, model checking, and a small exhaustive/Floyd–Warshall oracle. `witness.py`
contains finite-residue synthesis and checking. See `lean/INTEGRATION.md` for proposed
Lean modules and actual inspected integration hooks.

The source notes and bibliography identify public primary references. Third-party
source repositories and fonts are not copied into this archive. Original code and
text are provided under the included MIT license; cited works retain their own terms.
