# Validation record

What was checked, by whom, and what the check is worth. Merged from the one
proposal that wrote a narrative validation report and the five that recorded
machine-readable validation files.

## Checks performed by the nine original runs

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

These are nine separate suites over nine separate codebases. They cannot be
summed, and three of the nine ship no standalone test suite at all — their
assertions live inside the experiment driver, so `pytest` would pass vacuously
on those modules.

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

### Replay independence

Eight of nine runs ship a standalone replay command verified with site packages
disabled, so no numerical or symbolic search library is on the replay path. The
ninth replays in-process only.

This demonstrates that checking does not need the search machinery. It does
**not** demonstrate independent implementation: search and replay share the same
sparse polynomial and term representations in every prototype.

### Anti-vacuity guards

One run's replay program fails on a missing corpus rather than reporting
success on an empty directory, and mutates each decoded certificate to confirm
the checker actually rejects it. Another's bundle checker takes an explicit list
of the entries it is *required* to have verified, so a tampered status field
cannot pass vacuously. These are the right defaults and are worth generalising.

## Checks performed by this merge

| Check | Result |
| --- | --- |
| Merged article builds | pdfLaTeX, 68 pages, no errors, no undefined references |
| Core Lean elaboration | 3 of 17 files, Lean v4.34.0, no errors — see [`LEAN-STATUS.md`](LEAN-STATUS.md) |
| Bibliography deduplication | ~215 entries under ~100 keys reduced to 56 |
| Certificate corpus float scan | 1 float found across all nine runs; it is a timing field |
| Schema compatibility | semantically compatible, syntactically incompatible; one numeric conversion and a key-rename table reconcile all nine |

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
  cases, both drawn from the very dictionary their search covers.
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
3. Compiling the fourteen Mathlib-dependent Lean files against a built project.
4. A checker implemented independently from a specification, by someone who has
   not read the producer.
5. The controlled Lean evaluation described in Section 10 of the article.
6. An external audit.
