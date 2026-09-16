# Status and acceptance boundaries

## Executed

- Exact Python searches for anchored enclosures, differential ladders, rational
  tail barriers, harmonic minorants, and least-index accuracy witnesses.
- 246 certificate records accepted by a separately implemented sparse checker.
- Replay under `python -S` with search imports blocked.
- 738 evidence-bearing mutation rejections; 25 passing unit-test methods.
- SymPy coefficient/identity diagnostics; mpmath remainder samples at 120 digits.
- Exact finite-tail, harmonic-comparison, and rational witness checks.
- PDF compilation and rendered-page inspection (details in results/pdf-validation.json).

## Mathematical arguments, not formalized proofs

The article proves soundness of the three certificate families, a constructive
positive-shift lemma, convergence/divergence certificate construction for the
positive-leading rational fragment, and witness correctness. The local-germ
completeness statement describes an uncapped fair order/radius search, not a
completeness guarantee for the shipped fixed-radius bounded routine.

## Uncompiled candidates

`lean/SemanticBridges.lean` contains two small proof candidates without `sorry`
or user axioms. The file has NOT been compiled. It establishes neither checker
soundness nor an end-to-end source theorem from a generated certificate.

## Designed only

- Lean reification, source bridges, reflected checker soundness, and acceptance.
- Forge scheduler integration and LeanCert adapter.
- General rational anchors, two-sided intervals, arbitrary composition, symbolic scales.
- Stronger polynomial terminal checks for ladders.
- Signed rational-tail normalization and lower tail-potential certificates.
- Actual Lean benchmarks, kernel replay times, axiom audits, proof-size measurements.

## Important nonclaims

This does not install `forge`, benchmark any existing Lean tactic, or close
Leant/Djex's separate Church-indexing or universe-composition tasks. The numerical
samples do not prove universal claims. The Python checker is not formally verified
or fully hardened against hostile resource exhaustion. The unbounded rational-series
construction is mathematically complete in its stated fragment; resource-limited
software may still reject an oversized candidate or return unknown.

## Environment limitation

Python, SymPy, mpmath, and TeX were available. No `lean`, `lake`, or `elan` executable
was found. Execution-container attempts to clone GitHub repositories or install the
optional LeanCert bridge failed on DNS/network access. Source inspection was performed
through the connected GitHub read tools and official web documentation.

## Dependency observations

Forge's inspected README selects Lean v4.34.0. The inspected LeanCert toolchain and
Mathlib dependency select v4.33.1. They were not built together. The archive does not
supply a speculative Lake manifest. LeanCert's documented native and kernel trust
modes must be selected explicitly; its separate Li2 lightweight placeholder module
must not be confused with the actual verified declarations. The article gives the
specific source references and does not infer a defect in unrelated main checkers.
