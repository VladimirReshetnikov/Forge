# Run history

1. Implemented the producer and stdlib replay checker; all 24 initial fixtures
   generated and replayed, including cubic algebraic exceptional fibres.
2. During code review, removed algebraic elements' hash implementation because
   semantic equality may relate multiple representations and ordinary rationals.
   Caches now use representation keys; they are not semantic equality witnesses.
3. The initial differential run failed on a zero-polynomial conversion: Python
   `sum` returned an `int`, and the oracle attempted `.subs`. The traceback is
   preserved. Conversion now starts from `sympy.S.Zero`; the full differential
   suite then passed. No certificate-checking condition was weakened.
4. Enforced exact integer type for derivative indices, avoiding Python's
   Boolean-as-integer convention at that schema boundary.
5. Ran 540 targeted corruptions, 76 affine metamorphic cases, 42 pytest tests,
   complete no-site-package replay, and 237 selected-cell transport probes.
6. Added an individual solve/verify CLI and explicit nonzero exit status for
   failed example generation. These entry points were smoke-tested separately.
7. Compiled and visually checked the article PDF. Build logs and quality findings
   are retained in the results directory; intermediate TeX build files are not
   included in the final archive.

Only the initial differential exception was an observed failed experiment. The
hash and index changes were code-review hardening; no invalid theorem acceptance
was observed or is claimed to have been repaired by those changes.
