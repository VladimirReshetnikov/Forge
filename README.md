# Forge

**A certificate-producing proof-planning layer above Lean's `grind`.**

Start with **[`article/forge.pdf`](article/forge.pdf)** (128 pages). Its editable
source is in [`article/`](article/).

---

## What this is

A design for a broader Lean 4 automation system that keeps `grind` as its local
saturation engine and adds an outer layer which *changes the proof obligation*:
it selects induction principles, generalises accumulators, synthesises auxiliary
lemmas, constructs witnesses, obtains exact algebraic certificates, computes
closures that make an unbounded family finite, and returns exact quantities for
probabilistic and adversarial behaviour. Anything that succeeds must return
something Lean can check.

Alongside the design are Python prototypes of its central algorithms, the
certificates they produced, and the recorded evidence of twenty-seven separate
runs.

## What this is not

**`forge` is not an implemented Lean tactic.** Nothing here installs one.

None of the twenty-seven contributing efforts had a Lean executable available;
none of them compiled any Lean source, and none measured any comparison against
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
lean/           merged Lean sources: design contracts, closure principles, replays
results/        derived cross-run index, and the new measurements
docs/           status, sources, validation, and the Lean ledger
tools/          check_lean.py, build_results_index.py
proposals/      the twenty-seven original submissions, verbatim and frozen
```

`proposals/` is the provenance. Every claim in the merged draft is auditable
against it, and the twenty-seven runs' raw evidence stays there rather than
being copied or reformatted.

## Three rounds

The draft has been merged three times. The **design round** `p1`..`p9` came
first. The **extension round** `e1`..`e9` was prepared *against that merged
draft*, at commit `674521027d96`, and merged in turn. The **third round**
`r1`..`r9` was prepared against *that* result, at commit `c98e47c5`, and merged
in turn again.

That ordering matters for reading the evidence. No later round is a second
opinion on an earlier one: its proposals read the merged design, treat its
capabilities as prerequisites rather than contributions, and several open by
saying so. The third round read closely enough to correct this repository's own
status ledger — one of them notes that the merge records sixteen elaborated
core-only Lean files and that "it would therefore be wrong to say that nothing
in Forge has ever compiled".

Each round's contribution is a different kind of object. The second round
computes a **closure** — the smallest invariant object that settles a target —
rather than searching for a certificate in a fixed language, which is why the
article can state decision results and length bounds in §6 where §7 can only
state completeness relative to a dictionary. The third round adds three
subjects the document had no way to express: certificates where **order
matters** (§8), certificates over **transcendental** data (§9), and
certificates that return a **quantity** rather than a verdict (§10).

## Reading order

1. [`article/forge.pdf`](article/forge.pdf) — the design. §1–2 for the objective
   and the baseline, §5–10 for the algorithms, §13 for what was actually
   measured.
2. [`docs/STATUS.md`](docs/STATUS.md) — what is executed, what is generated but
   uncompiled, and what is designed only.
3. [`docs/LEAN-STATUS.md`](docs/LEAN-STATUS.md) — the Lean ledger, including
   the eighteen files this merge compiled and the one it found broken.
4. Appendix B of the article — the merge ledger: which proposal each idea came
   from, what was deduplicated, and how the twenty-seven's disagreements were
   resolved.
5. [`docs/IDEAS-FROM-LEANT-DJEX.md`](docs/IDEAS-FROM-LEANT-DJEX.md) — a review
   of two neighbouring projects that had already built the verification boundary
   this design only specified, and what was taken from them.

## The new results

All twenty-seven proposals recorded their Lean status as `NOT_RUN`. This
environment had `elan`, which installed the pinned
`leanprover/lean4:v4.34.0`, so every file importing nothing beyond Lean core
could be elaborated. **Eighteen files elaborate** — six in the merged tree, ten
across the extension proposals, two of the third round's three — and eleven of
them print `does not depend on any axioms` for every theorem they expose.

**And one does not.** The third round's remaining core-only file fails to parse:
it defines `prefix`, a reserved keyword in Lean 4, and all ten errors cascade
from that. The mathematics is fine and a rename repairs it. It is the only
delivered Lean in twenty-seven proposals that a compiler has contradicted,
because it is nearly the only delivered Lean a compiler has seen — and one
proposal, `r9`, declined to ship any Lean at all for exactly that reason. The
failure, its diagnosis and the tested repair are recorded together in
[`results/lean-round-three-elaboration.json`](results/lean-round-three-elaboration.json);
the archived source is left as delivered.

| File | Result |
| --- | --- |
| `lean/Forge/Design/Runtime.lean` | elaborated |
| `lean/Forge/Design/Contracts.lean` | elaborated |
| `lean/Forge/Examples/Structural.lean` | elaborated; two theorems use `propext` |
| `lean/Forge/Closure/Principles.lean` | elaborated; 8 theorems, no axiom dependencies |
| `lean/Forge/Closure/Covers.lean` | elaborated; 2 theorems, no axiom dependencies |
| `lean/Forge/Closure/Indexing.lean` | elaborated; 2 theorems, no axiom dependencies |
| `e1`…`e9` core specimens (10 files) | elaborated; 7 with no axiom dependencies |
| `r3`, `r7` core specimens (2 files) | elaborated; 1 with no axiom dependencies |
| `r8/lean/RankTelescoping.lean` | **failed to parse**; `prefix` is a keyword |

The three `Closure` files are the merge's own work: the ten core-only extension
specimens contained six spellings of one reachability theorem and five of one
word-fold theorem, so those are proved once here and the genuinely distinct
lemmas are kept and attributed. Recorded in
[`results/lean-core-elaboration.json`](results/lean-core-elaboration.json),
[`results/lean-extensions-elaboration.json`](results/lean-extensions-elaboration.json)
and
[`results/lean-closure-elaboration.json`](results/lean-closure-elaboration.json).

That is eighteen files of fifty-seven, with one more compiled and rejected. It is not an axiom audit, it does not
cover the twenty-one Mathlib-dependent files, it does not establish that any
checker is correct, and it is not a comparison against any tactic. **It also
does not change what any of those files says** — `e8`'s indexing sketch
type-checks and still proves an equation between two ordinary-list definitions,
which is exactly what its author claimed for it.

The second new result is a re-run. The design round's authoring environments
were unavailable here, but every later suite runs, and **all eighteen reproduce
their recorded counts** — on Python 3.14.4 rather than 3.13.5, so a reproduction
on different versions rather than a bit-identical replay. The third round's
eight replay corpora also return zero, covering 119, 228, 284, 246, 304, 520,
1,564 and 28,566 stored objects. Recorded in
[`results/extension-suites-rerun.json`](results/extension-suites-rerun.json) and
[`results/round-three-suites-rerun.json`](results/round-three-suites-rerun.json).

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
python tools/check_lean.py --mode elaborate lean/Forge/Design lean/Forge/Closure lean/Forge/Examples/Structural.lean
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

**The twenty-seven runs are not comparable and must never be summed** — not
within a round, and not across the three.

They look comparable. Five design-round runs recorded the seed `20260914`; five
extension-round runs recorded `20260915`, one day later on the same interpreter
and platform; and four third-round runs recorded `20260915` *again*, so the same
integer now labels runs in two different rounds over entirely unrelated
generators. That is a trap every time: the same seed drives entirely different
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

The third round's own files contain three more traps, all documented in §13 of
the article: two summaries reporting identical headline totals from different
runs, one corpus counted in two report files, and three different units that
look like one. A fourth is worth knowing before quoting any oracle-agreement
figure: when a bounded oracle reaches its limit it returns *no verdict*, and 39
such cases sit inside one proposal's records.

[`results/README.md`](results/README.md) has the detail;
[`results/certificate-counts.csv`](results/certificate-counts.csv) carries `run`
and `round` columns on every row and deliberately has no total. Its `outcome`
column matters as much as its counts: a row whose expected outcome is `refuted`
and whose `achieved` equals its `cases` is a fully successful row, because a
worker that returns a counterexample has answered the question.

## Where the merge came from

Twenty-seven independently prepared proposals for the same system, merged into
one draft. The originals are under `proposals/`. The design round was flattened
one level from the download-mangled directory names it arrived under:

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

The third round, likewise:

| | Emphasis |
| --- | --- |
| `r1-grammar-closure` | multilinear closure over trees; observable quotients |
| `r2-noncommutative` | two-sided receipts without completion; word Gram matrices |
| `r3-three-engines` | polyhedral projection, bounded completion, analytic jets |
| `r4-analytic-certificates` | ladders with rates below the input spectrum |
| `r5-analytic-extensions` | anchored remainders; series barriers and divergence |
| `r6-flow-ladders` | fixed-alphabet ladders with minimality receipts |
| `r7-quantitative` | six exact quantitative workers; the moment-transfer correction |
| `r8-alternation-probability` | parity games; couplings with Hall and Farkas duals |
| `r9-infinite-horizon` | pushdown summaries; Büchi duals; no Lean, deliberately |

Four of these nine wrapped their contents in a directory named differently from
the archive, so the slugs name what each package contains rather than what its
file was called.

Each slug names that submission's distinguishing emphasis. Appendix B of the
article records what each contributed, which ideas survive in exactly one
source, and how the twenty-seven's disagreements were resolved — always toward
the more conservative reading, and, where two similar-looking results turned out
not to be the same result, toward keeping the distinction. That judgement went
both ways in the third round: two of its noncommutative soundness theorems are
one theorem and its three integrating-factor lemmas are one lemma, so each is
stated once — but `r1`'s closure is *not* the closure already in §6, and merging
them would have destroyed the only quotient construction in the document.

## Licence

MIT-0, see [`LICENSE`](LICENSE). Cited works and referenced projects retain their
own terms; no third-party source, archive, or font file is redistributed here.
