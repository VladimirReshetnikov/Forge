# Ideas from Leant and Djex

A review of two neighbouring projects for material Forge could use.

- **[Djex](https://github.com/VladimirReshetnikov/Djex)** — a type-directed
  Haskell expression synthesizer merging Djinn (Dyckhoff's contraction-free
  **LJT**, terminating, able to prove uninhabitation) with Exference (ranked
  best-first search with typeclass evidence resolution).
- **Leant** — a Djex-powered synthesis REPL for Lean 4. `:synth` takes a type
  and constructs terms of it, ranked, **each candidate re-elaborated by Lean
  before the user sees it**.

## Why they matter here

Forge's weakest area is witness synthesis and type inhabitation. Its
implemented witnesses are all *arithmetic* — affine/Farkas, integer lattice,
modular residue, polynomial majorant. The bounded type-directed term
synthesiser for the higher-order fragment was specified by several proposals
and built by none.

More importantly: **all nine Forge proposals specified a verification boundary
and none implemented one.** Leant has. Not for certificates, but for term
synthesis — and the shape transfers.

## The headline findings

### 1. Two ways to accept a proof Lean never checked

Verified first-hand against the installed `leanprover/lean4:v4.34.0`, not taken
on the reviewed project's word — its analysis cites 4.33.0, so the claims
needed rechecking at our pinned version. **Neither appears in any of the nine
proposals.**

`Kernel.Environment.addDecl` branches on `debug.skipKernelTC` and calls
`addDeclWithoutChecking` when it is set. The option's registration says:
*"skip kernel type checker. WARNING: setting this option to true may compromise
soundness because your proofs will not be checked by the Lean kernel."* Default
`false`, but the value used is whichever `Options` the caller passes. A
verifier must **pin it off**, not merely decline to set it. Live for the
Boolean lane: v4.34.0's `bv_decide` docs list the same option as a supported
knob that disables checking the LRAT proof.

`Lean.addDecl` in `CoreM` goes through `env.addConstAsync`, commits preliminary
constant info *immediately*, and under `Elab.async` defers the kernel check to
a task. **The declaration is visible before it is checked.** An acceptance step
that adds a declaration and observes it is present has observed nothing.

→ Article §4, Invariant 6.

### 2. "No errors and no `sorry`" is not enough

A response with no error diagnostics, no `sorry` obligations **and no committed
environment** means the elaborator never committed a checked command at all.
Leant checks for a committed environment on three of its four verification
paths and omits it on the fourth — the "looks well-typed" hole, surviving in
production code that is otherwise meticulous.

→ Article §4, Invariant 7: acceptance requires a *positive* signal that the
checker ran.

### 3. The status lattice

The single highest-value artefact. A binary certificate / no-certificate split
under-specifies the system badly, and **every real integration lives in the
middle** — which is where a design silently upgrades a heuristic into evidence.
Eleven outcomes, each with its typical producer and the consequence it
*permits*, so permission is a property of the outcome rather than a local
decision by consuming code.

With three governing rules: evidence attaches to the exact tuple and no name
may stand in for it; guidance and authority are separate; and **pruning states
its approximation polarity** — an over-approximation may justify pruning when
even it is unsatisfiable, an under-approximation may produce witnesses but may
never justify pruning.

→ Article §4.

### 4. `unsat` is relative to the encoding

The cleanest articulation of Forge's UNKNOWN rule found anywhere. Djex types
every raw solver result as `RawObservationUse = HeuristicRankingOnly` — a
one-constructor permission type whose whole purpose is to make the permission
explicit and non-extensible at the call site. And it names the strength
`RawSolverUnsatRelativeToEncoding`.

The asymmetry is instructive. Forge's Farkas and lattice workers *earn* the
stronger claim, because their encodings are exact for their fragments and the
certificate is checked. Djex's spine-length abstraction does not, and it
refuses the temptation explicitly. Z3 is a **proposal generator for
counterexample inputs**: `sat` + model → extract integers → run the candidate's
own interpreter concretely → mint a receipt only if the contract is violated.
`unsat` buys nothing at all, not even pruning.

### 5. LJT is a decision procedure, not a certificate producer

Important correction, and it changed what the article now claims.

Djinn's negative answer is a single enumeration tag: no closed-branch tree,
no refutation object, nothing a second program can re-check. Soundness rests on
the implementation plus a translation gate. So it is *weaker* than Forge's
lattice worker, which emits a certificate whose checker verifies
`det U = ±1` without calling the elimination that produced `U`.

**The opportunity:** LJT is contraction-free and terminating, so a failed
search tree is finite and could be reified into a checkable refutation object.
Nobody has built this. It would give Forge a second *certificate-producing*
infeasibility worker.

> **Update: the extension round built it, by a different route.** `e4` supplies
> finite Kripke countermodels for IPC — a rooted finite partial order with a
> persistent valuation — and the checker *recomputes forcing* from scratch
> rather than trusting any solver-supplied table of formula truth values. That
> is the checkable refutation object this section asked for, and it is now the
> only one in the collection. It is not a reified LJT search tree; it is the
> semantic dual, and it arrives with the same discipline this section demands.
>
> Two things about its scope are worth copying rather than quietly widening.
> First, an accepted certificate means *there is no derivation of G from Gamma
> in the named IPC calculus* — not that Lean can prove `¬G`, not that no Lean
> term of `G` exists, and nothing about hypotheses omitted from the object
> sequent. Second, the enforcement tests are classical tautologies: excluded
> middle, double-negation elimination, Peirce's formula, propositional
> linearity. Each is classically valid, so an interface that turned any of their
> countermodels into a proof of the negated Lean formula would be visibly
> unsound. Those examples are not ornamental — they are how the worker's
> semantic ceiling is enforced in the test suite.
>
> A world bound is still a bound. When it is exhausted the answer is
> **unknown**: IPC having the finite model property does not turn a three-world
> cap into a decision procedure, and a valid schema that survives the search is
> a positive control against an invalid refuter, not a theorem.
>
> The worker is merged into `prototype/forge/closure/kripke.py`, and the
> correction above stands unchanged: the countermodel is the artefact, and the
> enumeration tag never was one.

### 6. The negative-evidence gate, as three conjuncts

```
search completed  ∧  translation lossless  ∧  no self-reference available
```

The middle one is computed by the **encoder, at translation time, before any
search runs** — so it is a property of the rendering and cannot be influenced
by how the search went. It is carried **per node**: every atom records whether
it is safe for refutation. An atom mentioning a concrete constant poisons a
negative verdict; so does an erased typeclass dictionary, because the
dictionary can carry data. The payoff is a message that *names the obstructing
symbols*.

The third conjunct buys a genuinely useful message for one extra bounded search
paid from leftover fuel: *"no non-recursive inhabitant exists; one exists if
the definition may call itself."* Safe because of a monotonicity rule — the
sharper claim may degrade to the weaker one, but exhausting the budget during
the diagnostic pass must never degrade an already-decided result to unknown.

→ Article §5.

### 7. The tactic is the interface; it need not be the executor

Forge assumed one axis of choice — how deeply to reach into `grind`'s
internals. There is a second and it matters more: **where the search runs.** A
native tactic searching in the Lean server process competes with elaboration,
can only be cancelled if it polls, can take the server down on a crash or OOM,
and has to keep sessions alive across commands — fighting incremental
recompilation for exactly the persistent obligation graph Forge wants.

→ Article §8: controller / worker / optional solver, with the controller
holding *"no authority to declare a candidate well-typed, a goal unprovable, or
a solver observation valid."*

### 8. Do not search in `Expr`

For a tactic step, searching in Lean's metavariable machinery is right. For a
bounded, accounted, certificate-producing search it costs the completeness
ledger, stable alpha-normal fingerprints, deterministic serialisation,
independent checking, exact step accounting, the ability to keep a dependent
region opaque without it being normalised away, and decoupling from Lean's
metavariable implementation.

### 9. Ranking is a capability

The boundary usually governs *admission* and leaves *presentation* ungoverned —
so a ranker can drop, duplicate, or reassociate a checked result with another's
evidence. Leant gives the ranker epoch-scoped opaque handles and validates that
what returns is a total injective map into what went out, **reconstructing the
output from the original receipts at the proposed indices**.

Related, and a silent failure: deduplicating by a lossy key (pretty-printed
text, alpha-equivalence, eta, proof irrelevance) can discard the representative
carrying the evidence and keep a look-alike.

### 10. The receipt as an abstract type

The constructive answer to Forge's "a type is not a check":

```haskell
-- Opaque receipt that the verification callback accepted a candidate.
-- This records only callback acceptance at this boundary. It is NOT
-- behavioral evidence, a solver certificate, or a kernel proof.
data Verified candidate = Verified candidate
type role Verified nominal
```

Module-private constructor; nominal role so no coercion can forge one; and
documentation that deliberately *under*-claims, fixing a ceiling everything
downstream must respect.

## Smaller items worth keeping

| Idea | Where |
| --- | --- |
| `example` not `def` — the check is ephemeral and mutates nothing | §4 |
| `noncomputable` — codegen failure is not a type error | §4 |
| `autoImplicit` **off** at a certificate boundary; on, a typo in the goal is silently generalised into an implicit parameter | §4 |
| Re-elaborate the **original goal text** every time; never cache the elaborated form | §4 |
| Transport failure is not semantic failure; and infrastructure degradation voids results computed under it | §4 |
| Two tiers: a fast in-session gate (~100–300 ms) and a slow out-of-session replay in a fresh process with an empty axiom inventory | §4 |
| Verification cost is architectural: if it dominates, lazy best-first with a quota *is* the design | §4 |
| A verification budget distinct from the search budget | §4 |
| Snapshot = opaque artefact + fingerprint + **tooling ABI**, rather than enumerating fields that will be incomplete at the next release | §8 |
| Invalidate every derived cache *atomically* with the snapshot | §8 |
| Environment **generation tokens**: undo restores an older environment while issuing a *new* token, so stale capabilities fail closed | §8 |
| Three levels of identity: Lean / neutral / presentation, the last "never sufficient to recover an authority" | §8 |
| The origin table never leaves the worker | §8 |
| One function for search-pruning and final-checking, parameterised by policy | §7 |
| Termination work at admission time (Paterson condition, superclass acyclicity, overlap rejection) | §7 |
| `Either error (Maybe receipt)` — budget-exhausted ≠ no-instance | §7 |
| Class obligations structurally disjoint from ordinary propositions | §7 |
| Deduplication never refunds budget | §3 |
| A branch dropped for a resource reason stays structurally visible to the top | §3 |
| Banks store re-checkable **inputs**, never verdicts; every reuse re-runs the check | §4 |
| Free probes before paid ones: all-zero origin probe, then bounded box, then the solver | — |
| Fingerprints are complete canonical encodings, not hashes, with a phantom subject parameter so two identity domains cannot be compared | §4 |
| Cache fingerprints must include solver version, invocation profile, parameters, encoding version | §4 |
| Glivenko: re-run on `¬¬G` decides classical propositional provability; quantified goals **skip** the fallback | §5 |
| Dependent subformulas that only need *transporting* alpha-normalise to opaque atoms and the goal is still decided | §5 |
| Universe correctness comes free from the kernel — the engine may be universe-sloppy and verification discards it | §5 |
| Anti-forgery on out-of-band channels: exactly-one-tag decoding; a dependent pair so erasure cannot hide a `sorry` | — |

## What Forge already had

The search/authority split; certificate-producing acceptance; snapshot and
restore; refusal rather than guessing; bounded budgets; heuristic ranking
separated from admission; and the rule that a failed bounded search is
UNKNOWN. The reviewed projects mostly *sharpen* these rather than add to them —
the exception being the verification boundary itself, which they have and Forge
does not.

## Documentation practices worth copying

Both projects do something the nine proposals did not, and it is cheap.

**A three-valued capability ledger.** Accepted / attempted-without-acceptance /
no-indexed-evidence — with an explicit note that the third is *not* a claim of
absence. "Not attempted" and "attempted and failed" are different facts with
different consequences for a reader deciding where to invest.

**Separate *Status* and *Acceptance required* columns,** with acceptance
criteria pinned to exact original parameters, plus an anti-substitution clause:
*"single, chained and generic-payload comparisons do not close this query."*

**Preserve failed-run receipts** as linked artefacts. *"Diagnostic failures are
not acceptance receipts"* is a one-line policy that prevents a large class of
drift.

**Disclaimers with mechanical consequences.** A module that says what it does
not prove, *and* whose fingerprint entrance fails closed as a result. If a
document says a worker cannot emit a disproof, there should be a type making it
impossible.

## Where this landed

| Finding | Article |
| --- | --- |
| `debug.skipKernelTC`, async `addDecl` | §4 — Invariant 6 |
| Committed environment as positive evidence | §4 — Invariant 7 |
| Status lattice + three governing invariants | §4 |
| Verification boundary implementation | §4 |
| Neighbouring tactics (`exact?`, `itauto`, `decide`, `omega`) | §2 |
| Negative verdicts; LJT; Glivenko; completeness ledger | §5 |
| Kripke countermodels — the refutation object §5 asked for, built by `e4` | §5, §6 |
| Instance obligations during synthesis | §7 |
| Tactic-as-interface / worker-as-executor | §8 |
| Three levels of identity; generation tokens | §8 |
| Do not search in `Expr` | §8 |
| Accounting rules (dedup, dropped branches) | §3 |
| Three-valued ledger | `STATUS.md` |
