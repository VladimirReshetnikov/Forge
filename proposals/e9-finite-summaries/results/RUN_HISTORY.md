# Run history

The authoritative delivered run is `run-4/`, produced by the delivered code.
It is one corpus; its counts are not combined with any upstream Forge run.

- Run 1: failed in common-left-multiple search because a zero polynomial had
  become a Python integer and did not support `.subs`. The original traceback
  is preserved as `failed-run-1-stderr.txt`. No acceptance result was written.
  Repair: coerce the zero expression to SymPy. A dedicated regression test passes.
- Run 2: passed the original corpus. It solved interior telescoping equations,
  then checked boundary equations on the returned candidates. Its summary,
  certificates, and original replay log are retained as historical evidence.
- Run 3: interrupted by the 45-second execution limit, before results were
  written. This happened while adding boundary equations to the search matrix.
  Inspection found that empty-product Python division could introduce a floating
  coefficient. Repair: use an explicit SymPy Rational multiplier and require
  every search matrix entry to be rational before nullspace calculation.
  The exact location of the timeout was not instrumented, so its cause is not
  established by a profile. The corrected implementation completed run 4.
- Run 4: boundary equations participate in search and are independently replayed.
  All 245 entries pass, as do 245 specified invalidating mutations and 41 unit
  tests. Two insufficient ansatz requests are recorded as UNKNOWN. Run 4 and its
  separate `python -S` replay supply the article's numbers.

Timing is single-run wall-clock evidence in this container, not a performance
claim against Lean tactics. The matrices of run 4 have more rows than run 2;
there is no controlled performance comparison between these historical runs.
