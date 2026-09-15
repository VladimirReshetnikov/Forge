# Implementation status

Merged from the eighteen proposals' status files, which appeared under a dozen
different names in several formats. The three-bucket model below is taken from
the clearest of them.

Machine-readable twin: [`status.json`](status.json).

## Executed

Implemented in Python and actually run, in at least one of the eighteen runs.
Section 10 of the article says which run, with what result, and under what
caveat.

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

## Generated but not compiled

Produced as Lean source, never checked by a compiler — with one exception.

- Cone certificate replays (two emitter styles, 18 theorems)
- A 32-leaf Bernstein subdivision replay
- Accumulator-invariant replays, powers 0–8
- The orbit/orbit_invariant framework and 49 instances
- Power-sum and affine-witness replays
- Hand-written arithmetic, lattice, residue, cross-theory and mixed specimens

**The exceptions.** Sixteen files import nothing beyond Lean core and now
elaborate against `leanprover/lean4:v4.34.0`: six in the merged tree (the
runtime contract, the certificate-soundness contract, the Mathlib-free
structural proofs, and three new `Forge/Closure` files holding the induction
principles the closure workers lower to) and ten across the extension
proposals. Ten of the sixteen print `does not depend on any axioms` for every
theorem they expose. See [`LEAN-STATUS.md`](LEAN-STATUS.md).

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
- The eighteen runs' counts are not comparable and were never pooled — not
  within a round, and not across the two rounds, which attack overlapping
  problems and would double-count.
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
