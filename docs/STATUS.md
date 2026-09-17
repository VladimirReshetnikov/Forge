# Implementation status

Merged from the thirty-six proposals' status files, which appeared under some
twenty-five different names in several formats. The three-bucket model below is taken from
the clearest of them.

Machine-readable twin: [`status.json`](status.json).

## Executed

Implemented in Python and actually run, in at least one of the thirty-six
runs. Section 18 of the article says which run, with what result, and under
what caveat.

- Exact sparse rational polynomial arithmetic, with canonical-form enforcement
  and float rejection
- Exact quadratic decomposition by symmetric pivoting / Schur complement
- Finite polynomial-cone search: LP proposal, exact rational repair, independent
  identity check
- Equality-ideal multipliers with unrestricted sign
- Bernstein box subdivision with checked coverage trees, in three split policies
- Square-factor and Sturm certificates for univariate intervals *(one run only)*
- Polynomial recurrence synthesis, direct-solve and CEGIS variants
- Accumulator-invariant synthesis, including the state-machine formulation
- Affine witness synthesis with Farkas multipliers *(one run only)*
- Integer-lattice witness extraction with divisibility obstructions *(one run
  only)*
- Finite-residue witness synthesis *(one run only)*
- Polynomial witness synthesis certified by cone certificates *(one run only)*
- Demand-directed ground Horn reasoning, propositional and first-order
- Typed equational prover with structural-induction trace replay
- Accumulator generalisation and bounded lemma synthesis
- Proof-logging CDCL(T) over integer difference logic, in two certificate
  formats
- Standard-library-only replay of every stored certificate
- Lean source emission for cone, Bernstein, induction and witness certificates
- Mutation, corruption, differential and negative-control test suites

From the extension round:

- Target-directed observable-space closure over a finite alphabet, with the
  sharp `D-1` separating-word bound and delayed-error fixtures that attain it
- Target-generated polynomial-ideal closure with reconstructed multipliers, and
  tracked Buchberger multiplier extraction
- Descending (greatest-fixed-point) space iteration, with constant multipliers
  and with bounded-degree polynomial multipliers
- Finite-state all-words contracts checked against an independent oracle, and
  shortest distinguishing words
- Finite-algebra covers for inductive datatypes, with concrete counterexample
  trees under an earlier-child-index discipline
- Boundary-safe binomial-power telescoping with shifted-support flux, including
  the geometric weight and the parametric order-two family
- Ore common-left-multiple certificates, singularity-aware seed plans, and a
  complete natural-root cover from an explicit Cauchy bound
- Exact one-output integer projection: guard, hash-consed straight-line witness
  program, and Bezout receipts
- Finite Kripke countermodels for intuitionistic propositional logic, with a
  bounded rooted-tree proposer and an independent forcing replay
- Continuation-local synthesis over derived local algebra contracts
- Ranking synthesis for supplied cyclic call graphs, with exact descent replay
- Re-run of all nine extension suites in a second environment, reproducing
  every recorded count

From the third round:

- Many-sorted multilinear reachable-span closure over derivation trees, with a
  context-free trace compiler and compressed derivation witnesses
- Sibling-conditioned one-hole-context closure and exact observable quotients
  verified by finite commuting diagrams
- Two-sided free-algebra ideal certificates, by bounded context elimination and
  by bounded Grobner-Shirshov completion (two lanes, one soundness theorem)
- Degree-complete homogeneous reasoning with truncated-quotient matrix
  countermodels
- Unique word Gram matrices for homogeneous degree 2d with exact rational
  LDL^T, adjoint sandwiches, and involution ray generators
- Mixed-strictness polyhedral projection over ordered fields, with min/max
  witness DAGs and complete pair-coverage receipts
- Integrating-factor ladders for rational exponential polynomials, in three
  variants: auxiliary rates below the spectrum, a fixed alphabet with a
  minimality receipt, and an unstructured search
- Anchored rational remainder certificates preserving the order of vanishing,
  for exp, sin, cos, log(1+ax) and arctan
- Rational-series upper barriers with Cauchy-modulus witnesses, and harmonic
  divergence certificates with least-index witnesses
- Vanishing-jet certificates for non-strict zeros, with a bounded automatic
  anchor/order selector
- Exact maximum MDP reachability, uniform expected hitting-time bounds, and
  polynomial drift potentials on infinite numeric state spaces
- Parity games with positional strategies and threshold-local ranks; Buchi and
  co-Buchi dual ranks with a visit budget
- Exact optimal transport with Farkas duals and Hall obstructions; alternating
  probabilistic simulation by coupling
- Unbounded-stack pushdown summaries with proof-sharing DAGs and closed
  exclusion relations
- Re-run of all nine third-round suites and eight replay corpora in a second
  environment, reproducing every recorded count

From the fourth round:

- Exact minimal coverability frontiers for ALL initial markings of a
  place/transition net, with a positive run per basis element
- Guarded compressed-run summary algebra, productive-transition acceleration,
  positive self-covering lassos, and guarded endpoint equivalence
- Certified scalar population thresholds and multiparameter Pareto frontiers
- Backward antichains for finite-control counter systems with multi-ray
  nonnegative affine initial families
- Matrix-update transition systems (reset, transfer, merge, duplication) and
  finite-control lossy FIFO under the subsequence order
- A direct-cover receipt that certifies a predecessor obligation without
  materialising its 26,075,972,546 minimal elements
- Exact equality-register transducer equivalence over an infinite atom alphabet
- Exact rational enclosures of irrational least fixed points of probabilistic
  polynomial systems, with inverse-free weighted Newton certificates
- Critical and subcritical extinction certificates, and isolated scalar
  algebraic least roots
- Bivariate real quantification by certified cell covers, with piecewise
  root-index witnesses and counterstrategies
- Uniform real-fiber count circuits over the same cover, by Hermite quadratic
  forms and Descartes-exact reasoning
- First-order arithmetic over unbounded naturals by binary-automatic
  predicates, with zero-tail saturation and regular least-witness graphs
- Complete stabilizer-chain certificates with certified non-membership,
  coset-cover canonical images, exact symmetric/alternating recognition, cycle
  inventories, and sparse Reynolds projection
- Integral homology coordinates, certified chain reductions with witness
  transport, and adjoint obstructions to chain homotopy
- Re-run of every round-four suite and all seven replay corpora in a second
  environment

## Generated but not compiled

Produced as Lean source and, until recently, never checked by a compiler. The
thirteen Mathlib files of this kind merged into `lean/Forge` now compile on the
pinned toolchain (`results/lean-mathlib-forge.json`), and so do 34 of the 44
proposal copies and emitted files (`results/lean-mathlib-sweep.json`).

- Cone certificate replays (two emitter styles, 18 theorems)
- A 32-leaf Bernstein subdivision replay
- Accumulator-invariant replays, powers 0–8
- The orbit/orbit_invariant framework and 49 instances
- Power-sum and affine-witness replays
- Hand-written arithmetic, lattice, residue, cross-theory and mixed specimens

**The exceptions.** Forty files are Mathlib-free, and **39 of them
elaborate** against `leanprover/lean4:v4.34.0`: eight in the merged tree,
fourteen in the new `Forge.Checker`, three in the design-round proposals, ten across the
extension proposals, two of the third round's three, and both of the fourth
round's two. Twelve print `does not depend on any axioms` for every theorem they
expose.

**And fourteen of them are no longer specimens.** `Forge.Checker` implements
most of Gate 2 of the design: certificate checkers with proved soundness for the
cone, affine-witness, Farkas, recurrence and invariant families; typed
reification with a proved bridge; the `forge_cone` tactic; and `forge_cone?`,
which calls the prototype's search through a bounded data protocol. Gate 1, the
orchestration layer the design puts first, has its first milestone in
`Forge.Frontend`: fixed-order workers, rollback, proof-term audit, replay record.

**And two files that do not compile.** The third round's third core-only file
defines `prefix`, a reserved keyword. And `r6`'s `FlowTargets.lean` places a
module docstring above its `import`, which Lean 4 rejects at parse time whether
or not Mathlib is present; it was missed by every earlier scan because it
imports Mathlib and was assumed to fail for that reason. Those are the only two
pieces of delivered Lean in thirty-six proposals that a compiler has
contradicted, because they are nearly the only delivered Lean a compiler has
seen.

**And one scan of ours that was wrong.** The first round-four run reported a
file as containing a `sorry`. Its only occurrence of the token was the sentence
in its own header saying there were none. The scanner now strips Lean comments
before searching; re-auditing all 90 Lean files finds **zero** real `sorry` or
`sorryAx` anywhere in this repository. See
[`LEAN-STATUS.md`](LEAN-STATUS.md).

Elaboration does not change what a file says. `e8/lean/IndexingSketch.lean`
type-checks and still proves an equation between two ordinary-list definitions;
it does not close the Church-encoded query its author declined to claim it
closed.

## Designed, not implemented

Specified in the article, in some cases in considerable detail, and built by
nobody.

- The `forge` tactic and its user-facing syntax
- The obligation graph and scheduler against real Lean snapshots
- The `grind` adapter, incremental or otherwise
- A dependent-type-aware reifier, and any proof that a reified problem
  corresponds to a Lean expression
- Reflected Lean checkers for any certificate family, and their soundness
  theorems
- A Lean formalisation of the Sturm root-count theorem — without which the
  univariate worker cannot be trusted in Lean, and which the extension round's
  root-cover worker would also rather reuse than reimplement
- A source reifier for any closure fragment: affine folds, summary
  homomorphisms with proved constructor compatibility, or signed-lower-index
  binomials
- The cyclic-obligation compiler: tagged proposition families, well-founded
  relations from accepted ranks, and per-node local constructors
- A representation law connecting Church-encoded inputs to `List.foldr` at a
  fixed carrier and universe selection
- An exact LP or MILP backend for lexicographic rank synthesis with exported
  pivots and coefficient witnesses
- General quantifier instantiation, E-matching, and model-guided instantiation
- Higher-order and dependent-type witness synthesis
- External SMT / ATP proof reconstruction with residual-obligation handling
- A semidefinite backend with exact rational recovery
- Certified product envelopes (specified, never coded)
- Bounded equality saturation over real Lean expressions
- The axiom-policy audit
- A real Lean corpus evaluation, or any head-to-head comparison against `grind`

## How to read the three buckets

The buckets above are three-valued on purpose, and the third value is the one
that usually goes missing. Borrowed from the capability ledgers in Leant and
Djex:

| Marker | Means |
| --- | --- |
| **Executed** | ran, with a recorded result |
| **Generated but not compiled** | produced, never checked by a compiler |
| **Designed, not implemented** | specified; nobody built it |

An item in the third bucket is **not** a claim that it was tried and failed.
"Not attempted" and "attempted without success" are different facts with
different consequences for anyone deciding where to invest, and conflating them
is how a roadmap quietly turns into an apology.

Two practices go with this. The first is not in place yet; the second now
partly is.

- **Acceptance criteria pinned to exact parameters.** A row should say what
  would close it, in the original terms, with an anti-substitution clause where
  a near-miss exists — *"a bounded variant does not close this"*.
- **Failed runs preserved as linked artefacts.** A diagnostic failure is not an
  acceptance receipt, and deleting it is how a later reader mistakes silence
  for success. Four extension proposals do this: `e9` ships a `RUN_HISTORY.md`
  with three failures and their tracebacks — including one whose diagnosis it
  explicitly declines to claim it proved — and `e1`, `e3` and `e5` retain
  failed-run directories and diagnostic logs beside their accepted results.

## What is explicitly not claimed

- No Lean tactic named `forge` exists.
- No certificate anywhere has been checked by Lean's kernel.
- No comparison against `grind`, Aesop, `nlinarith`, LeanHammer, or any other
  tactic was performed by anyone.
- No speedup, solved-goal gain, or success-rate claim is made.
- The Python checkers are not formally verified, and several share
  representation code with the searches they audit.
- Neither the checkers nor the decoders are hardened against hostile input.
- The thirty-six runs' counts are not comparable and were never pooled — not
  within a round, and not across the four rounds, which attack overlapping
  problems and would double-count.
- Sixteen runs across three rounds record the seed `20260915`, over sixteen
  unrelated generators. A matching seed in this repository is not evidence of a
  shared corpus.
- Three proposals independently computed the *same* three-element mutual-
  exclusion antichain. That is one result. A ledger counting it three times is
  wrong by a factor of three on the collection's most quotable example.
- Two round-four proposals each report exactly twelve unit-test methods. The
  lists share no name and no subject.
- Three specific pooling traps in the third round's own recorded files are
  documented rather than silently avoided: two summaries with identical
  headline totals from different runs, one corpus counted in two report files,
  and three different units that look like one. See section 13 of the article.
- A bounded oracle that reaches its limit returns no verdict. Thirty-nine such
  cases are counted among one proposal's records; "250/250 oracle agreement"
  would be a fabrication and the correct decomposition is 70 + 141 + 39.
- A represented length is not an executed one. Two proposals report runs of
  2^60 and 2^31-1 steps computed from DAGs of 61 and 31 nodes; concrete
  expansion was checked only to small depth, and both say so.
- The extension suites' re-run reproduces recorded counts on different
  interpreter and library versions. It is not a bit-identical replay, no
  timings were compared, and it establishes nothing about checker correctness.
- Three different producer/checker separations are reported in this repository
  and they are not equivalent: a genuinely opposite computation, a replacement
  of search entry points during replay, and — in `e8`'s integer projection —
  a reconstruction using the same assembler as the search, disclosed by its own
  author.
- A bounded search returning nothing means **unknown**, never that a statement
  is false.
