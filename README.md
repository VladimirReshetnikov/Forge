# Forge

**A certificate-producing proof-planning layer above Lean's `grind`.**

Start with **[`article/forge.pdf`](article/forge.pdf)** (150 pages). Its editable
source is in [`article/`](article/).

---

## What this is

A design for a broader Lean 4 automation system that keeps `grind` as its local
saturation engine and adds an outer layer which *changes the proof obligation*:
it selects induction principles, generalises accumulators, synthesises auxiliary
lemmas, constructs witnesses, obtains exact algebraic certificates, computes
closures that make an unbounded family finite, returns exact quantities for
probabilistic and adversarial behaviour, and exhibits finite bases for infinite
sets of states. Anything that succeeds must return something Lean can check.

Alongside the design are Python prototypes of its central algorithms, the
certificates they produced, and the recorded evidence of thirty-six separate
runs.

And, new, **one certificate family implemented in Lean end to end**: a checker,
a proof that the checker is sound, and the prototype's own certificates run
through it and accepted by the Lean kernel. See
[`lean/Forge/Checker/`](lean/Forge/Checker/). It is a small part of the design.
It is the part that is no longer a proposal.

## What this is not

**`forge` is not an implemented Lean tactic.** Nothing here installs one.
`Forge.Checker` is a checker with a soundness proof, which is a different and
smaller thing: applying a certificate to a goal is a generated `have` and a
`simp`/`omega`, not automation that finds the certificate for you.

None of the thirty-six contributing efforts had a Lean executable available;
none of them compiled any Lean source, and none measured any comparison against
`grind`, Aesop, `nlinarith`, LeanHammer, or any other tactic. No speedup and no
solved-goal gain was claimed anywhere in them.

That is still the right description of the **proposals**. It is no longer the
description of this repository: `Forge.Checker` compiles, its soundness theorem
is proved, and the comparison against `grind` and `nlinarith` has now been run.
What that comparison showed is in
[`lean/Forge/Checker/README.md`](lean/Forge/Checker/README.md) and §18 of the
article --- and it is a comparison on a handful of problems, not a benchmark.

The Python checkers are research code. They are not formally verified, they
share representation code with the searches they audit, and they are not
hardened against hostile input. **A passing Python check is not a Lean-kernel
proof.** The one exception is the cone family: those certificates are now
re-checked by the Lean kernel in
[`lean/Forge/Checker/Corpus.lean`](lean/Forge/Checker/Corpus.lean), by
`decide` rather than `native_decide`, so nothing there rests on the compiler.
The other twelve families are Python-checked only.

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
proposals/      the thirty-six original submissions, verbatim and frozen
```

`proposals/` is the provenance. Every claim in the merged draft is auditable
against it, and the thirty-six runs' raw evidence stays there rather than being
copied or reformatted.

## Four rounds

The draft has been merged four times. The **design round** `p1`..`p9` came
first. The **extension round** `e1`..`e9` was prepared *against that merged
draft*, at commit `674521027d96`. The **third round** `r1`..`r9` was prepared
against *that* result, at `c98e47c5`. The **fourth round** `s1`..`s9` was
prepared against *that* result, at `58ea206`, and merged in turn again.

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
certificates that return a **quantity** rather than a verdict (§10). The fourth
adds five more: **finite bases** for infinite state spaces (§11), decisions over
the **reals** by certified cell covers (§12), **automatic** arithmetic on
unbounded naturals (§13), **group** certificates including certified
non-membership (§14), and **integral homology** with obstructions to chain
homotopy (§15).

## Reading order

1. [`article/forge.pdf`](article/forge.pdf) — the design. §1–2 for the objective
   and the baseline, §5–15 for the algorithms, §18 for what was actually
   measured.
2. [`docs/STATUS.md`](docs/STATUS.md) — what is executed, what is generated but
   uncompiled, and what is designed only.
3. [`docs/LEAN-STATUS.md`](docs/LEAN-STATUS.md) — the Lean ledger: the twenty
   files this merge compiled, the one it found broken, and the defect it found
   in its own scanner.
4. Appendix B of the article — the merge ledger: which proposal each idea came
   from, what was deduplicated, and how the thirty-six's disagreements were
   resolved.
5. [`docs/IDEAS-FROM-LEANT-DJEX.md`](docs/IDEAS-FROM-LEANT-DJEX.md) — a review
   of two neighbouring projects that had already built the verification boundary
   this design only specified, and what was taken from them.

## The new results

All thirty-six proposals recorded their Lean status as `NOT_RUN`. This
environment had `elan`, which installed the pinned
`leanprover/lean4:v4.34.0`, so every file importing nothing beyond Lean core
could be elaborated. Twenty-eight files are Mathlib-free, and
**27 of them elaborate** — six in the merged tree, three in the design-round
proposals, ten across the extension proposals, two of the third round's three,
and both of the fourth round's two. Twelve print `does not depend on any
axioms` for every theorem they expose.

The three design-round proposal files turned up late, and the reason is worth
knowing: every round's scan looked at the merged tree and at that round's own
proposals, and nobody went back over `p1`–`p9`'s own `lean/` directories. All
three import only `Lean`, all three elaborate, and all three carry a header
saying they were not compiled.

**And one does not.** The third round's remaining core-only file fails to parse:
it defines `prefix`, a reserved keyword in Lean 4, and all ten errors cascade
from that. The mathematics is fine and a rename repairs it. It is the only
delivered Lean in thirty-six proposals that a compiler has contradicted,
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
| `s3`, `s5` core specimens (2 files) | elaborated; 1 with no axiom dependencies |

The three `Closure` files are the merge's own work: the ten core-only extension
specimens contained six spellings of one reachability theorem and five of one
word-fold theorem, so those are proved once here and the genuinely distinct
lemmas are kept and attributed. Recorded in
[`results/lean-core-elaboration.json`](results/lean-core-elaboration.json),
[`results/lean-extensions-elaboration.json`](results/lean-extensions-elaboration.json)
and
[`results/lean-closure-elaboration.json`](results/lean-closure-elaboration.json).

That is 27 of the 28 Mathlib-free files — counting transitively, so a file
importing a sibling that is itself Mathlib-free counts as Mathlib-free. The
other 58 depend on Mathlib and **nothing has ever checked any of them** — and
the one time this merge looked inside that bucket for a reason unrelated to
Mathlib, it found a second broken file. `r6`'s `FlowTargets.lean` puts a module
docstring above its `import`, which Lean 4 rejects at parse time whether or not
Mathlib is present. So the count of delivered Lean a compiler has contradicted
is two, not one.

**And one defect in our own tooling.** The first round-four scan reported a file
as containing a `sorry`. Its only occurrence of the token was the sentence in
its own header saying there were none — the scanner tested for a substring and
so reported exactly backwards. It now strips Lean comments first, with a depth
counter because Lean block comments nest. Re-auditing **all 86 Lean files**
finds **zero** real `sorry` or `sorryAx` anywhere in this repository; all 25
occurrences are authors stating there are none. That is a better result than
anyone claimed, and it could not have been established before, because the
unfixed scanner could not tell the two cases apart. It is not an axiom audit, it does not
cover the twenty-one Mathlib-dependent files, it does not establish that any
checker is correct, and it is not a comparison against any tactic. **It also
does not change what any of those files says** — `e8`'s indexing sketch
type-checks and still proves an equation between two ordinary-list definitions,
which is exactly what its author claimed for it.

The second new result is a re-run. The design round's authoring environments
were unavailable here, but every later suite runs, and **all twenty-six
reproduce their recorded counts** — on Python 3.14.4 rather than 3.13.5, so a reproduction
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
transport with singularity seed plans.

Three fourth-round lanes are merged under `forge/wsts/`: place/transition
frontiers with compressed witness runs, finite-control counter systems with
parameterised initial families, and matrix-update systems with lossy FIFO
channels. Those three proposals, plus a fourth, wrote one well-quasi-order, one
antichain, one predecessor formula and one saturation loop three or four times
between them; each is written once here, and only the model languages and their
predecessor rules are still spelled out separately. The three-element
mutual-exclusion antichain that three of them computed independently is stored
once, as one result.

All eight merged lanes are standard library only with their *searches*
included, so both subpackages run under `python -S`.

Six lanes are deliberately **not** merged, because folding them in would cost
the merged package the property that makes its replay evidence worth anything:

| Lane | Needs |
| --- | --- |
| Ideal closure (`e1`, `e3`, `e6`, `e7`) | a Gröbner engine |
| Telescoping (`e2`, `e3`, `e6`, `e9`) | exact bivariate nullspaces |
| All of the third round (`r1`–`r9`) | a noncommutative Gröbner engine, interval arithmetic over transcendental constants, exact linear programming |
| Probabilistic fixed points (`s2`) | shares the word "coverability" with `s1` and nothing else |
| Register transducers (`s3`) | finite by the Bell numbers, not by any well-quasi-order |
| Real cell covers (`s5`, `s6`) | a computer-algebra producer |

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

**The thirty-six runs are not comparable and must never be summed** — not
within a round, and not across the four.

They look comparable. Five design-round runs recorded the seed `20260914`; five
extension-round runs recorded `20260915`; four third-round runs recorded
`20260915` *again*; and **seven of round four's nine** recorded it as well.
Sixteen runs across three rounds now carry one integer over sixteen unrelated
generators — Petri nets, real-root covers, binary automata, permutation groups,
chain complexes and more. That is a trap every time: the same seed drives entirely different
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

A different kind of duplication is worth knowing before quoting the
collection's most readable example: **three round-four proposals independently
computed the same three-element mutual-exclusion antichain.** Verified directly
— the nets are identical under a coordinate bijection. It is one result, and a
ledger counting it three times is wrong by a factor of three.

The third round's own files contain three more traps, all documented in §18 of
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

The fourth round:

| | Emphasis |
| --- | --- |
| `s1-resource-frontiers` | coverability frontiers for *all* initial markings |
| `s2-unbounded-certificates` | one-marking coverability; irrational least fixed points |
| `s3-infinite-state-workers` | counter systems; equality registers |
| `s4-ordered-certificates` | matrix updates and lossy FIFO; separation receipts |
| `s5-witness-atlases` | bivariate real quantification; root-index witnesses |
| `s6-real-fibers` | uniform real-fiber counts over the same cover |
| `s7-automatic-arithmetic` | binary-automatic arithmetic; least-witness graphs |
| `s8-certified-symmetry` | stabiliser chains; canonical images; Reynolds projection |
| `s9-constructive-exactness` | integral homology; homotopy obstructions |

Four of these nine do backward-antichain coverability — the largest
single-subject cluster in the collection — and §11 merges them rather than
printing four adjacent accounts of one idea.

Each slug names that submission's distinguishing emphasis. Appendix B of the
article records what each contributed, which ideas survive in exactly one
source, and how the thirty-six's disagreements were resolved — always toward
the more conservative reading, and, where two similar-looking results turned out
not to be the same result, toward keeping the distinction. That judgement went
both ways in the third round: two of its noncommutative soundness theorems are
one theorem and its three integrating-factor lemmas are one lemma, so each is
stated once — but `r1`'s closure is *not* the closure already in §6, and merging
them would have destroyed the only quotient construction in the document.

## Licence

MIT-0, see [`LICENSE`](LICENSE). Cited works and referenced projects retain their
own terms; no third-party source, archive, or font file is redistributed here.
