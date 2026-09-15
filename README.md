# Forge

**A certificate-producing proof-planning layer above Lean's `grind`.**

Start with **[`article/forge.pdf`](article/forge.pdf)** (68 pages). Its editable
source is in [`article/`](article/).

---

## What this is

A design for a broader Lean 4 automation system that keeps `grind` as its local
saturation engine and adds an outer layer which *changes the proof obligation*:
it selects induction principles, generalises accumulators, synthesises auxiliary
lemmas, constructs witnesses, and obtains exact algebraic certificates. Anything
that succeeds must return something Lean can check.

Alongside the design are Python prototypes of its central algorithms, the
certificates they produced, and the recorded evidence of nine separate runs.

## What this is not

**`forge` is not an implemented Lean tactic.** Nothing here installs one.

None of the nine contributing efforts had a Lean executable available; none of
them compiled any Lean source, and none measured any comparison against `grind`,
Aesop, `nlinarith`, LeanHammer, or any other tactic. No speedup and no
solved-goal gain is claimed anywhere.

The Python checkers are research code. They are not formally verified, they
share representation code with the searches they audit, and they are not
hardened against hostile input. **A passing Python check is not a Lean-kernel
proof.**

A bounded search that finds nothing returns **unknown**. It never means the
statement is false.

Baseline: Lean **v4.34.0** (released 14 September 2026), Mathlib
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`.

## Layout

```
article/        the merged draft — start at forge.pdf
prototype/      merged Python package: exact arithmetic, search, checkers
lean/           merged Lean sources: design contracts, generated replays, specimens
results/        derived cross-run index, and the one new measurement
docs/           status, sources, validation, and the Lean ledger
tools/          check_lean.py, build_results_index.py
proposals/      the nine original submissions, verbatim and frozen
```

`proposals/` is the provenance. Every claim in the merged draft is auditable
against it, and the nine runs' raw evidence stays there rather than being copied
or reformatted.

## Reading order

1. [`article/forge.pdf`](article/forge.pdf) — the design. §1–2 for the objective
   and the baseline, §5–7 for the algorithms, §9 for what was actually measured.
2. [`docs/STATUS.md`](docs/STATUS.md) — what is executed, what is generated but
   uncompiled, and what is designed only.
3. [`docs/LEAN-STATUS.md`](docs/LEAN-STATUS.md) — the Lean ledger, including the
   one thing this merge was able to add.
4. Appendix B of the article — the merge ledger: which proposal each idea came
   from, what was deduplicated, and how the nine's disagreements were resolved.
5. [`docs/IDEAS-FROM-LEANT-DJEX.md`](docs/IDEAS-FROM-LEANT-DJEX.md) — a review
   of two neighbouring projects that had already built the verification boundary
   this design only specified, and what was taken from them.

## The one new result

All nine proposals recorded their Lean status as `NOT_RUN`. This environment had
`elan`, which installed the pinned `leanprover/lean4:v4.34.0`, so the three
files that import nothing beyond Lean core could be elaborated:

| File | Result |
| --- | --- |
| `lean/Forge/Design/Runtime.lean` | elaborated, no errors |
| `lean/Forge/Design/Contracts.lean` | elaborated, no errors |
| `lean/Forge/Examples/Structural.lean` | elaborated, no errors |

Recorded in [`results/lean-core-elaboration.json`](results/lean-core-elaboration.json).

That is three files of sixteen. It is not an axiom audit, it does not cover
the thirteen Mathlib-dependent files, it does not establish that any checker is
correct, and it is not a comparison against any tactic.

## Building the article

```bash
cd article
pdflatex -interaction=nonstopmode forge.tex
pdflatex -interaction=nonstopmode forge.tex
pdflatex -interaction=nonstopmode forge.tex
```

Plain pdfLaTeX with stock TeX Live or MiKTeX packages. No `fontspec`, no system
fonts to install, no bibliography tool, no shell escape. (The nine sources
between them needed four engines and nine font families; dropping that was
deliberate.)

## Running the prototypes

```bash
cd prototype
python -m pip install -r requirements.txt
python -m pytest -q
```

To replay stored certificates without any search library installed:

```bash
python -S bin/verify.py
```

`-S` disables site packages, so this cannot reach NumPy, SciPy or SymPy. It is
useful evidence that checking is separable from search — and it is still Python
verification, not a Lean proof.

Re-running an experiment writes to `reproduced-results/`, which is gitignored,
so a fresh run cannot overwrite a recorded one.

## Checking the Lean sources

Core only, no Mathlib needed:

```bash
python tools/check_lean.py --mode elaborate lean/Forge/Design lean/Forge/Examples/Structural.lean
```

Everything, against a project with Mathlib already built:

```bash
python tools/check_lean.py --mode lake --project /path/to/mathlib-project lean
```

Expect failures on the Mathlib-dependent files. They were written against an
inspected source tree, never against a running compiler. The remedy is to fix
the script — not to insert `sorry`, and not to weaken a condition until a check
passes.

## Reading the numbers

**The nine runs are not comparable and must never be summed.**

They look comparable: same day, same library versions, and five of them recorded
the same seed value. That is a trap. The same seed drives entirely different
generators over entirely different case sets — 30 cone cases in one run, 1,080
witness tables in another, 1,500 differential SAT cases in a third. Three runs
record no seed at all. And "cases", "checks", "assertions", "tests",
"certificates" and "bundles" are five different units.

[`results/README.md`](results/README.md) has the detail;
[`results/certificate-counts.csv`](results/certificate-counts.csv) carries a
`run` column on every row and deliberately has no total.

Two properties *do* hold across all nine: no mathematical coefficient anywhere
in the certificate corpus is a float, and every stored certificate replays
without the search libraries.

## Where the merge came from

Nine independently prepared proposals for the same system, merged into one
draft. The originals are under `proposals/`, flattened one level from the
download-mangled directory names they arrived under:

| | Original |
| --- | --- |
| `p1-structural-search` | `FORGE_Beyond_Grind(1) (1)/` |
| `p2-obligation-controller` | `Forge-design-and-prototypes/` |
| `p3-planner-certificate-layer` | `Forge_Beyond_Grind/` |
| `p4-theory-cooperation` | `Forge_Beyond_Grind(1)/` |
| `p5-certificate-first` | `Forge_Tactic_Design/` |
| `p6-proof-logging-cdcl` | `forge-beyond-grind/` |
| `p7-successor-architecture` | `forge-grind/` |
| `p8-obligation-broker` | `forge-tactic-design-and-prototypes/` |
| `p9-proof-planner` | `forge_beyond_grind (1)/` |

Each slug names that submission's distinguishing emphasis. Appendix B of the
article records what each contributed, which ideas survive in exactly one
source, and how the nine's disagreements were resolved — always toward the more
conservative reading.

## Licence

MIT-0, see [`LICENSE`](LICENSE). Cited works and referenced projects retain their
own terms; no third-party source, archive, or font file is redistributed here.
