# Run history and evidence strength

1. Read the pinned repository/status/source evidence and primary mathematics.
   Direct container network cloning was unavailable (DNS resolution failure),
   so public source inspection used the available GitHub and web tools. This
   did not affect local Python execution.
2. Implemented exact reachable-span search, context quotient, source frontends,
   and independent replay. The initial named-fixture smoke run accepted the
   positive, negative, and quotient fixtures.
3. Added and ran 18 unittest methods. All passed, including 240 finite-language
   differential cases, 40 quotient certificates, and 20 designed invalid objects.
4. Added a paired-derivation finite oracle for quotient preservation and reran
   the full recording script. All 40 cases agree on corresponding inputs, not
   merely as sets of possible outputs. The final results retain complete inputs
   and certificates so these observations can be checked again.
5. Replayed eight named fixture certificates in fresh isolated Python processes
   to which only checker.py was copied. All accepted. No producer/compiler
   imports or third-party libraries were available in those processes.
6. Added solve.py, exercised its input-audit/search/replay path on tree_identity,
   and independently replayed the emitted certificate. See results/cli-smoke.json.
7. The first LaTeX build failed because a double-bracket macro required an
   unavailable command. Replaced it with ordinary paired brackets. Subsequent
   PDF layout review caught a wide correspondence diagram and a spilled title
   note; these were reformatted. Final PDF build and rendered-page review are
   recorded separately in results/pdf-validation.json.

No mathematical test expectation or checker identity was weakened in response
to a failed test. The recorded unit suites passed; the failures above were
network retrieval and document-production issues, not accepted certificates.

## Unexecuted work

lean/ReplayLeafCount.lean is a hand-written specimen, NOT_RUN because neither
lean nor lake was installed. No generic reflected checker, native source
reifier, or native forge tactic was implemented. No external tactic benchmark
was attempted. Further integration proposals in the article remain proposals.

## Important evidence distinctions

- A Python positive certificate establishes acceptance by this executable
  checker, not a Lean-kernel proof.
- A quotient certificate establishes preservation diagrams, not minimality.
- The completed mathematical search has a least-reachable/context-closure
  interpretation; the checker need not certify search optimality.
- A counterexample is relative to the independently supplied original abstract
  source. A future Lean adapter must prove the source correspondence.
- A resource cutoff is UNKNOWN. It never gives a negative theorem.
- Test methods, generated cases, observations, and certificate identities are
  distinct units and are not pooled.
