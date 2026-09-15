# Executed run history

1. Initial smoke examples checked the scaled graph, coupled graph, nonlinear
   fold equivalence, and its one-constant mutation under both modes.
2. The first corpus runner failed while constructing a Python result row:
   `accepted` was supplied both explicitly and through a checker receipt.
   This reporting bug was repaired. Its log and the one prepared problem are
   isolated in `results/failed-run-01/`; no accepted outcome is taken from it.
3. A sequential corpus invocation was interrupted by the enclosing execution
   timeout after writing a prefix of exact run records. It had no completed
   summary. The follow-up used explicit resumption and six worker processes.
   Existing problems/evidence were checked for exact agreement rather than
   substituted. The search algorithms and algebraic limits were unchanged.
   The external process timeout was increased from 15 to 30 seconds; no run
   in the accepted ledger reports either timeout. All unknowns are degree caps.
4. The completed ledger has 62 original problems, 124 mode runs, 108 accepted
   evidence files and 16 unknowns. Mixed concurrency means timings are diagnostic,
   not a controlled speed comparison.
5. All 40 regression test methods passed. One contains an additional 80-instance
   scalar differential test, separately counted from the main corpus.
6. A fresh `python -S` process replayed all 108 evidence files without importing
   search or SymPy. Its exact receipts are retained.
7. The Lean emitter produced 254 identity declarations for 45 positive ideal
   certificates. The compilation runner found no Lake executable and recorded
   NOT_RUN for every file. There was no Lean kernel or axiom audit.

The article distinguishes ordinary mathematical arguments, executed Python
results, source emission, and proposed/unexecuted integration.
