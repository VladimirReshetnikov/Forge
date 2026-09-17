# Validation record

What was checked, by whom, and what the check is worth. Merged from the
proposals that wrote narrative validation reports and the ones that recorded
machine-readable validation files.

## Checks performed by the thirty-six original runs

### Test suites

| Run | Framework | Count | Unit |
| --- | --- | ---: | --- |
| p1 | pytest | 275 | test instances |
| p2 | unittest | 31 | test methods, several with multiple seeded trials |
| p3 | assertions in driver | 1,680 | assertions |
| p4 | pytest | 64 | tests; parametrized tests contain further inner cases |
| p5 | pytest | 73 | tests |
| p6 | assertions in driver | 1,500 | differential SAT cases |
| p7 | assertions in driver | 833 | component cases, yielding 891 certificate checks |
| p8 | pytest | 260 | tests |
| p9 | pytest | 69 | tests |

Extension round:

| Run | Framework | Count | Unit |
| --- | --- | ---: | --- |
| e1 | unittest | 40 | tests |
| e2 | unittest | 13 | test methods, 69 subtests |
| e3 | unittest | 12 | test methods, 313 subtests |
| e4 | pytest | 151 | tests |
| e5 | pytest | 117 | test items |
| e6 | pytest | 318 | tests |
| e7 | unittest | 29 | test methods, 140 subtests |
| e8 | unittest | 21 | test methods, 19 of them mutation cases |
| e9 | unittest | 41 | tests |

Third round:

| Run | Framework | Count | Unit |
| --- | --- | ---: | --- |
| r1 | unittest | 18 | test methods |
| r2 | unittest | 57 | test methods, one holding 24 subtests |
| r3 | unittest | 12 | test methods |
| r4 | unittest | 18 | test methods |
| r5 | unittest | 25 | test methods |
| r6 | unittest | 22 | test methods |
| r7 | unittest | 24 | test methods, run under both `-S` and `-O -S` |
| r8 | unittest | 14 | regression methods |
| r9 | unittest | 36 | test methods |

Fourth round:

| Run | Framework | Count | Unit |
| --- | --- | ---: | --- |
| s1 | unittest | 68 | test methods |
| s2 | — | — | no unit suite; replay corpus and in-experiment assertions |
| s3 | unittest | 27 | test methods |
| s4 | combined runner | — | `run_tests.py` reporting `REPLAY_OK` |
| s5 | pytest | 42 | test items (the only round-four suite needing pytest) |
| s6 | unittest | 25 | test methods |
| s7 | unittest | 7 | interface tests |
| s8 | unittest | 12 | test methods |
| s9 | unittest | 12 | test methods |

These are thirty-six separate suites over thirty-six separate codebases. They
cannot be summed, and four of them ship no standalone test suite at all --- three
of the design-round nine and `s2` — their assertions live inside the experiment driver, so
`pytest` would pass vacuously on those modules.

**Twenty-six of the thirty-six were re-run here**, in a different environment,
and every recorded count was reproduced. The design round's nine authoring
environments were unavailable, so their counts could only be read. Eight of the
third round's nine and seven of the fourth round's nine also ship a replay
entry point, and every one of them returns zero. See
[`../results/round-three-suites-rerun.json`](../results/round-three-suites-rerun.json)
and
[`../results/round-four-suites-rerun.json`](../results/round-four-suites-rerun.json).

Unlike the design round, **every extension suite was re-run here**, in a
different environment, and every recorded count was reproduced. See
[`../results/extension-suites-rerun.json`](../results/extension-suites-rerun.json).
Two notes from that re-run: `e8` runs under `python -S`, which is how it
demonstrates its standard-library-only claim; and `e9`'s suite must be invoked
from `prototype/`, which is a path convention and not a defect.

### Negative controls and corruption rejection

This is the part of the evidence that carries the most weight, because it tests
the thing that matters: that a checker refuses a bad certificate.

| Run | What was rejected |
| --- | --- |
| p1 | mutated targets, weights, hypotheses, recurrence base terms, affine offsets, Bernstein split points, child nodes, claimed bounds, Sturm chains |
| p2 | negative square weights, changed targets, omitted domain constraints, incorrect witness coefficients, inexact certificate values, negative slacks, missing children, boundary split points, invalid axes, wrong-tail induction, self-referential rules, corrupt rewrite paths, ill-sorted terms |
| p3 | 4 quadratic negative controls, 7 Bernstein corruptions, 18 induction corruptions |
| p4 | corrupted rational weights, polynomial coefficients, hypothesis indices, Bernstein split locations and coverage, induction generalisation data, constructor-case coverage, theorem order and status, theory-cycle evidence, resolution pivots, proof roots |
| p5 | 24 false polynomials, all returning unknown; a float-tolerance exploit with weight `(10²⁰+1)/10²⁰`; cone tampering; Bernstein cover tampering |
| p6 | 222 truncated certificates, 2 mutated theory certificates, 12 induction mutations on the synthesis side and 12 more under independent replay |
| p7 | 330 corrupted certificates |
| p8 | float weights, out-of-range indices, arity mismatches, hypothesis-order-sensitive mixed certificates |
| p9 | parametrized bad-input matrices for cone, box, Horn and induction — including base-case use of the induction hypothesis, invalid generalisation metadata, rigid-variable intrusion, and reference to an unavailable future lemma |
| e1 | wrong pullback coefficients, fabricated targets, corrupted closure identities |
| e2 | 188 mutations across four families, each with a recorded rejection reason |
| e3 | 25 targeted invalid mutations, all rejected |
| e4 | malformed orders, broken persistence, a root that forces the goal, solver-supplied truth tables |
| e5 | 818 generated mutations, 0 accepted |
| e6 | 148 rejection controls alongside 84 differential cases |
| e7 | 31 corruptions: wrong action matrices, missing transitions, changed initialisations, a fabricated target combination, floating-point and non-canonical rationals, omitted call edges, erased phases, wrong lexicographic pivots, missing natural-domain proofs, captured binders, an outer-index escape, a wrong predecessor, changed Church semantics, wrong ideal multipliers, reversed non-commuting execution order |
| e8 | 19 mutation cases: matrix and multiplier corruption, wrong initial behaviour, an insufficient multiplier budget, an empty or unsafe cover, a self-referential tree, a good state falsely designated bad, changed Bézout coefficients, deleted feasibility guards, a changed witness node, floats and Booleans where exact integers are required |
| e9 | 245 specified invalidating mutations, one per stored object, all rejected |

`e9`'s mutation design is worth singling out because it is the most precise:
each mutation is chosen to change a *specific* checked quantity — one added to a
telescoper's last operator coefficient, so the interior residual changes by the
nonzero polynomial `R_r`; a separating word's claimed nonzero output replaced by
zero; the first required seed removed from a plan. It is also the only package
that states the converse: scaling a valid telescope by a nonzero rational
produces another valid certificate and *should* be accepted, so "every syntactic
change is rejected" is not the claim.

### Independence checks

Several checkers deliberately run *algorithmically opposite* to the producers
they audit. This is the strongest structural evidence available short of formal
verification.

- A Bernstein checker that **expands** a claimed basis representation and
  compares it against an independently computed affine transform, sharing no
  conversion formula with the search that proposed it (p3, p5, p8).
- A SAT checker that **re-derives** each added clause by independent unit
  propagation rather than replaying the solver's resolution chain (p6).
- A theory-lemma checker that **duplicates** the atom-negation rule instead of
  calling the solver's shared edge constructor, so a bug in one copy cannot
  cancel itself out in the other (p6).
- A Sturm checker that **recomputes the entire chain** rather than trusting a
  stored root count (p1).
- A lattice checker that verifies `det U = ±1` by independent rational
  elimination, without calling the extended-gcd construction that produced `U`
  (p7).
- An invariant replay that **ignores** the certificate's own diagnostic residual
  field and recomputes it, so a fabricated `"residual": 0` cannot serve as
  evidence (p6).
- Differential cross-checks against a symbolic algebra library (p1, p3, p7, p8,
  p9) and against exhaustive enumeration (p4, p6).
- A finite-state closure checked against an **independently written full-closure
  oracle** on every case, 240 of them (e3), and again on 100 random finite
  algebras (e8).
- A backward invariant-space algorithm cross-checked against a **forward
  feature-span** algorithm on 72 affine systems, agreeing in every case (e7).
- A Gröbner oracle comparison: 368 polynomial remainders against SymPy and 185
  traced basis identities replayed independently (e7).
- An **exhaustive concrete oracle** over a provably sufficient integer range —
  `[-B-P, B+P]`, where `B` bounds the right sides and `P` is the lcm of the
  moduli — agreeing with the generated feasibility guard on all 3,400 parameter
  valuations (e8).
- Word search compared against exhaustive evaluation of every word up to the
  proved distinguishing length, 1,140 evaluations over 100 models (e9).

Two of these deserve their qualifications repeated. The e7 forward/backward pair
shares its exact scalar-arithmetic helper, so it is algorithmic differential
testing rather than two wholly independent implementations. And the e8 oracle is
complete *for the generated test inputs* because of the stated range argument —
it is not an arbitrary small box, and it is also not a proof.

### Replay independence

Eight of nine runs ship a standalone replay command verified with site packages
disabled, so no numerical or symbolic search library is on the replay path. The
ninth replays in-process only.

This demonstrates that checking does not need the search machinery. It does
**not** demonstrate independent implementation: search and replay share the same
sparse polynomial and term representations in every prototype.

The extension round makes that qualification precise, and the three levels are
not equivalent:

| Strength | What replay does | Where |
| --- | --- | --- |
| Strongest | A genuinely different computation from the search — no Gröbner basis verified, no Buchberger re-run, no zero-remainder flag trusted; rational matrices multiplied and compared where the search solved nullspaces | e7 ideal lane, e9 all lanes |
| Middle | Search entry points replaced by exceptions before replay; input-table semantics still shared | e8 invariant and finite lanes |
| Weakest | The witness reconstructed with *the same assembler* the search used | e8 integer projection |

The weakest case is disclosed by the package that built it, which is the
behaviour to reward: replay there catches a modified receipt or program but
cannot catch an arithmetic mistake common to both uses of the assembler, and the
mitigation is the exhaustive concrete oracle above, not checker independence.
`e9` similarly discloses that its producer and checker share one exact-arithmetic
module.

### Anti-vacuity guards

One run's replay program fails on a missing corpus rather than reporting
success on an empty directory, and mutates each decoded certificate to confirm
the checker actually rejects it. Another's bundle checker takes an explicit list
of the entries it is *required* to have verified, so a tampered status field
cannot pass vacuously. These are the right defaults and are worth generalising.

Three more from the extension round belong in the same list:

- **No producer-asserted residual field is accepted at all.** `e9`'s decoder has
  no such field; the checker reconstructs the residual from the authoritative
  problem and the supplied coefficients and requires an empty canonical
  dictionary. This is stronger than ignoring a supplied field, because it cannot
  be re-introduced by a careless later revision.
- **Structural shape checks precede every mathematical identity**, and the
  loader rejects duplicate JSON keys, non-finite numeric constants, and files
  above 32 MiB.
- **An empty result is not a refutation.** `e8` states that an empty invariant
  packet is a vacuously valid preservation certificate and must not be upgraded
  to a mathematical claim that no useful invariant exists. The same discipline
  appears in `e4`: an exhausted world bound yields unknown, and the eight
  IPC-valid schemas in its corpus are positive controls against an invalid
  refuter, not statements proved by the absence of a countermodel.
- **A producer-supplied root list is not accepted.** `e9`'s checker verifies a
  Cauchy bound and enumerates `[0, B]` itself rather than trusting the search's
  claim to have found all the roots.

## Checks performed by this merge

| Check | Result |
| --- | --- |
| Merged article builds | pdfLaTeX, no errors, no undefined references or citations |
| Core Lean elaboration, merged tree | 6 of 21 files, Lean v4.34.0, no errors |
| Core Lean elaboration, extension round | 10 of 20 source files, no errors |
| Core Lean elaboration, design-round proposals | 3 of 3 core-only files (never scanned before) |
| Core Lean elaboration, third round | 2 of 3 core-only files; **1 fails to parse** |
| Core Lean elaboration, fourth round | 2 of 2 files |
| Core Lean elaboration, all rounds | **39 of 40** Mathlib-free files (transitively) |
| **`Forge.Checker` soundness proved** | **yes** — `Cert.sound`, `propext` + `Quot.sound` only |
| **Prototype certificates checked by the Lean kernel** | **3 of 3** cone certificates, via `decide` |
| Mathlib-importing file that also fails to parse | **1** (`r6`), found by sweeping all 86 files |
| Theorems printing no axiom dependencies | 12 of the 23 elaborated files |
| Third-round suites re-run | 9 of 9 pass; 8 of 8 replay corpora return zero |
| Fourth-round suites re-run | 8 of 8 existing suites pass; 7 of 7 replay corpora return zero |
| **`sorry` audit, all 90 Lean files** | **0 real occurrences**; 26 mentions, all in comments denying them |
| **Certificate benchmark** | 30/30 verified; **6/6 negative controls rejected** |
| **`grind` on the same 30** | 0/30 — and it cannot prove `0 ≤ x^2`, so this measures its scope |
| **Axiom audit, every `Forge.Checker` theorem** | **593 theorems**, all within `propext`/`Quot.sound` but one documented, necessary exemption; the audit fails the build otherwise |
| **Adversarial review of Gate 2** | 85+ attacks across three reviews; **0 false statements accepted**; findings fixed and pinned |
| **Mutation rejection at the data boundary** | every `forge_cone?` corruption case rejected; the id-injection attack refused by every exporter |
| **`forge_cone` facts composed with `grind`** | a goal neither `grind` nor `omega` proves alone, closed after one `have` |
| Extension suite re-run | 9 of 9 suites pass; 9 of 9 recorded counts reproduced |
| Bibliography deduplication | ~215 entries under ~100 keys reduced to 56 |
| Certificate corpus float scan | 1 float found across all nine design-round runs; it is a timing field |
| Design-round schema compatibility | semantically compatible, syntactically incompatible; one numeric conversion and a key-rename table reconcile all nine |
| Extension-round schema compatibility | **not** reconcilable by renaming: e7, e8 and e9 name closure certificates differently because their checkers accept different objects |

See [`LEAN-STATUS.md`](LEAN-STATUS.md) for the elaboration detail and
[`../results/README.md`](../results/README.md) for the re-run.

## What none of this establishes

Stated plainly, because the list above is long enough to be mistaken for more
than it is.

- **Not formal verification.** The Python checkers are hand-written research
  code. Passing tests is evidence about programs; it is not a proof.
- **Not kernel verification.** No certificate anywhere has been checked by
  Lean's kernel.
- **Not independence.** Search and replay share representation code. "Replay
  without the search libraries" is a weaker property than it sounds.
- **Not coverage.** Manufactured examples favour the grammar that generated
  them — most visibly for the 40 square certificates and the 100 generated cone
  cases, both drawn from the very dictionary their search covers. The extension
  round adds its own constructed positives: e7's twelve power-curve fixtures
  with known invariants, e9's forty comparison models built by invertible
  coordinate changes, e8's forty-eight affine-diagonal instances built to
  preserve the diagonal, and the forty-eight zero-relation-space controls among
  e7's seventy-two affine systems. Each package labels these as constructed.
- **Not reproduction.** The extension re-run reproduces recorded counts on
  *different* interpreter and library versions. It is not a bit-identical
  replay, and no timings were compared.
- **Not comparison.** No head-to-head against `grind`, Aesop, `nlinarith`,
  LeanHammer, or any other tactic exists anywhere in this work.
- **Not security.** No decoder here is hardened for hostile input. Several have
  sensible bounds; none is a service.

## What would raise assurance next

In rough order of value per unit of work:

1. A Lean formalisation of the certificate-checker semantics, starting with the
   cone checker, which is the smallest and most reused.
2. Property-based generation of malformed inputs, rather than the hand-written
   corruption lists above.
3. Compiling the twenty-one Mathlib-dependent Lean files, across both rounds,
   against a built project.
4. A checker implemented independently from a specification, by someone who has
   not read the producer.
5. The controlled Lean evaluation described in Section 10 of the article.
6. An external audit.

One item on this list has been partly answered by the collection itself, and
the answer is worth recording: **stop shipping uncompiled Lean.** Round four
did, without being asked, after one round-three proposal argued the point and a
compiler agreed with it. Seven of its nine proposals ship a statement of
obligations instead of a theorem file, which is both more honest and more
useful.

Before any of the rest, there is still a five-minute item: **compile the Lean
that already exists.** Thirty-four
delivered files import Mathlib and have never been checked by anything. The one
time a compiler was pointed at previously-unchecked delivered Lean, it found a
file that does not parse. That is not a criticism of its author — it is a
measurement of what an uncompiled file is worth as evidence.

One further target is smaller than the rest and should come before them: prove
a single source theorem end to end through the cheapest checker in the
repository. The finite-algebra cover verifies a bare list of state identifiers
by membership, distinctness, constructor closure and inclusion. Getting one Lean
theorem out of that lane — with a recorded axiom inventory, and re-run without
the proposer — would establish more than another thousand Python certificates.
