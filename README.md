# Forge

**A certificate-producing proof-planning layer above Lean's `grind`.**

Start with **[`article/forge.pdf`](article/forge.pdf)** (111 pages). Its editable
source is in [`article/`](article/).

---

## What this is

A design for a broader Lean 4 automation system that keeps `grind` as its local
saturation engine and adds an outer layer which *changes the proof obligation*:
it selects induction principles, generalises accumulators, synthesises auxiliary
lemmas, constructs witnesses, obtains exact algebraic certificates, and computes
closures that make an unbounded family finite. Anything that succeeds must
return something Lean can check.

Alongside the design are Python prototypes of its central algorithms, the
certificates they produced, and the recorded evidence of eighteen separate runs.

## What this is not

**`forge` is not an implemented Lean tactic.** Nothing here installs one.

None of the eighteen contributing efforts had a Lean executable available; none
of them compiled any Lean source, and none measured any comparison against
`grind`, Aesop, `nlinarith`, LeanHammer, or any other tactic. No speedup and no
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
results/        derived cross-run index, and the new measurements
docs/           status, sources, validation, and the Lean ledger
tools/          check_lean.py, build_results_index.py
proposals/      the eighteen original submissions, verbatim and frozen
```

`proposals/` is the provenance. Every claim in the merged draft is auditable
against it, and the eighteen runs' raw evidence stays there rather than being
copied or reformatted.

## Two rounds

The draft was merged twice. The **design round** `p1`..`p9` was merged first.
The **extension round** `e1`..`e9` was then prepared *against that merged
draft*, at commit `674521027d968d59f7b83220ed52304a85cb55e2`, and merged in
turn.

That ordering matters for reading the evidence. The second round is not a second
opinion on the first: its proposals read the merged design, treat its
capabilities as prerequisites rather than contributions, and several open by
saying so. Their contribution is a family of workers that compute a **closure**
— the smallest invariant object that settles a target — rather than searching
for a certificate in a fixed language. That is why the article can state
decision results and length bounds in §6 where §7 can only state completeness
relative to a dictionary.

## Reading order

1. [`article/forge.pdf`](article/forge.pdf) — the design. §1–2 for the objective
   and the baseline, §5–8 for the algorithms, §10 for what was actually
   measured.
2. [`docs/STATUS.md`](docs/STATUS.md) — what is executed, what is generated but
   uncompiled, and what is designed only.
3. [`docs/LEAN-STATUS.md`](docs/LEAN-STATUS.md) — the Lean ledger, including the
   two things this merge was able to add.
4. Appendix B of the article — the merge ledger: which proposal each idea came
   from, what was deduplicated, and how the eighteen's disagreements were
   resolved.
5. [`docs/IDEAS-FROM-LEANT-DJEX.md`](docs/IDEAS-FROM-LEANT-DJEX.md) — a review
   of two neighbouring projects that had already built the verification boundary
   this design only specified, and what was taken from them.

## The new results

All eighteen proposals recorded their Lean status as `NOT_RUN`. This environment
had `elan`, which installed the pinned `leanprover/lean4:v4.34.0`, so every file
importing nothing beyond Lean core could be elaborated. **Thirteen files
elaborate**: three in the merged tree and ten across the extension proposals.
Seven of the ten print `does not depend on any axioms` for every theorem they
expose.

| File | Result |
| --- | --- |
| `lean/Forge/Design/Runtime.lean` | elaborated |
| `lean/Forge/Design/Contracts.lean` | elaborated |
| `lean/Forge/Examples/Structural.lean` | elaborated; two theorems use `propext` |
| `e1`…`e9` core specimens (10 files) | elaborated; 7 with no axiom dependencies |

Recorded in
[`results/lean-core-elaboration.json`](results/lean-core-elaboration.json) and
[`results/lean-extensions-elaboration.json`](results/lean-extensions-elaboration.json).

That is thirteen files of thirty-eight. It is not an axiom audit, it does not
cover the twenty-one Mathlib-dependent files, it does not establish that any
checker is correct, and it is not a comparison against any tactic. **It also
does not change what any of those files says** — `e8`'s indexing sketch
type-checks and still proves an equation between two ordinary-list definitions,
which is exactly what its author claimed for it.

The second new result is a re-run. The design round's authoring environments
were unavailable here, but every extension suite runs, and **all nine reproduce
their recorded counts** — on Python 3.14.4 rather than 3.13.5, so a reproduction
on different versions rather than a bit-identical replay. Recorded in
[`results/extension-suites-rerun.json`](results/extension-suites-rerun.json).

## Building the article

```bash
cd article
pdflatex -interaction=nonstopmode forge.tex
pdflatex -interaction=nonstopmode forge.tex
pdflatex -interaction=nonstopmode forge.tex
```

Plain pdfLaTeX with stock TeX Live or MiKTeX packages. No `fontspec`, no system
fonts to install, no bibliography tool, no shell escape. (The design-round
sources between them needed four engines and nine font families; dropping that
was deliberate.)

## Running the prototypes

The merged package:

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

Five extension lanes are merged into that package, under `forge/closure/`:
observable-space closure with separating words, finite-algebra covers with
counterexample trees, exact integer projection, Kripke countermodels, and Ore
transport with singularity seed plans. All five are standard library only with
their *searches* included, so the whole subpackage runs under `python -S`.

Two lanes are deliberately **not** merged. Target-generated ideal closure needs
a Gröbner engine and boundary-safe telescoping needs exact bivariate
nullspaces, so neither search can be standard-library-only, and folding them in
would cost the merged package the property that makes its replay evidence worth
anything.

The nine extension packages remain under `proposals/e*/prototype/` and run from
there; each proposal's README gives its own command, and
[`results/extension-suites-rerun.json`](results/extension-suites-rerun.json)
records all nine as re-run here. Two conventions are worth knowing: `e8` runs
under `python -S`, which is how it demonstrates its standard-library-only
claim, and `e9`'s suite must be invoked from its own `prototype/` directory.

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
inspected source tree, never against a running compiler, and several were
emitted programmatically by a prototype that could not test its own output —
`e4` alone generated 222 local obligations that way. The remedy is to fix the
script. It is not to insert `sorry`, and not to weaken a condition until a check
passes.

## Reading the numbers

**The eighteen runs are not comparable and must never be summed** — not within a
round, and not across the two.

They look comparable. Five design-round runs recorded the seed `20260914`; five
extension-round runs recorded `20260915`, one day later on the same interpreter
and platform. That is a trap both times: the same seed drives entirely different
generators over entirely different case sets — 30 cone cases in one run, 1,080
witness tables in another, 1,500 differential SAT cases in a third. And "cases",
"checks", "assertions", "tests", "certificates", "bundles", "records",
"attempts" and "objects" are nine different units.

Across the rounds there is a second reason. The extension proposals re-derive
several design-round results in a stronger certificate language, so a combined
total would count the same mathematics twice under different names. Two of them
say so explicitly about their own counts.

One more distinction to carry: **"every certificate replays" means three
different things here.** At the strongest, the checker performs a genuinely
different computation from the search. In the middle, the search entry points
are replaced by exceptions during replay. At the weakest — `e8`'s integer
projection, disclosed by the proposal that built it — the checker reconstructs
the answer with the same assembler the search used, so replay catches a modified
certificate but not an arithmetic mistake common to both.

[`results/README.md`](results/README.md) has the detail;
[`results/certificate-counts.csv`](results/certificate-counts.csv) carries `run`
and `round` columns on every row and deliberately has no total. Its `outcome`
column matters as much as its counts: a row whose expected outcome is `refuted`
and whose `achieved` equals its `cases` is a fully successful row, because a
worker that returns a counterexample has answered the question.

## Where the merge came from

Eighteen independently prepared proposals for the same system, merged into one
draft. The originals are under `proposals/`. The design round was flattened one
level from the download-mangled directory names it arrived under:

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

The extension round, with its distinguishing emphasis:

| | Emphasis |
| --- | --- |
| `e1-relational-closure` | span and ideal lanes over one problem set |
| `e2-algorithmic-extensions` | inductive subspaces; Gosper and creative telescoping |
| `e3-closure-extensions` | four lanes; an independent oracle on every finite-state case |
| `e4-delta-countermodels` | finite Kripke countermodels; machine reachability |
| `e5-finite-certificates` | observable-space closure with the sharp `D-1` bound |
| `e6-finite-certificates-b` | three lanes reported by outcome kind, not success rate |
| `e7-capability-extensions` | continuation-local synthesis; cyclic descent |
| `e8-invariant-ideals` | bounded-multiplier invariants; covers; integer projection |
| `e9-finite-summaries` | weighted words; boundary-safe telescoping; Ore transport |

Two of them ship a PDF under the same filename, `forge-extensions.pdf`. They are
different documents by different authors and are kept apart rather than merged
by name.

Each slug names that submission's distinguishing emphasis. Appendix B of the
article records what each contributed, which ideas survive in exactly one
source, and how the eighteen's disagreements were resolved — always toward the
more conservative reading, and, where two similar-looking results turned out not
to be the same result, toward keeping the distinction.

## Licence

MIT, see [`LICENSE`](LICENSE). Cited works and referenced projects retain their
own terms; no third-party source, archive, or font file is redistributed here.
