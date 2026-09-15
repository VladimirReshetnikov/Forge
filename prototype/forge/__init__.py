"""Forge: one merged prototype assembled from nine independent proposals.

Each module names the proposal it was based on and what was folded into it.
Nothing in the import path of this package pulls in NumPy, SciPy or SymPy: those
are imported inside the search functions that actually need them, so every
CHECKER can run under `python -S` with the standard library alone.

  poly         p1 + p8 + p3 + p7     exact sparse rational polynomials
  linalg       p7 + p2 + p1          exact RREF, LP-proposal-then-exact-repair
  certificates p1 + p5               every checker, no search code
  cone         p5 + p7 + p8          cone / dictionary-SOS search
  quadratic    p1 + p3               exact Schur-complement decomposition
  bernstein    p8 + p3 + p2          box subdivision search
  univariate   p1 (verbatim)         square-factor + Sturm certificates
  recurrence   p1 + p2 + p7 + p5     recurrence / accumulator invariants
  terms        p9 + p3 + p4          typed first-order terms
  induction    p4 + p2 + p9          structural induction + trace replay
  horn         p5 + p8 + p9 + p3     demand-directed Horn search
  sat          p6 + p4               CDCL(T) + integer difference logic
  witness.*    p2/p1, p7, p4, p9     affine, lattice, modular, polynomial
  io.decode    p1 + p3 + p9 + p6     hardened stdlib-only decoding
  io.lean      p5 + p1 + p7 + p3     Lean source emission
"""
from . import (poly, linalg, certificates, cone, quadratic, bernstein, univariate,
               recurrence, terms, induction, horn, sat, witness, io)  # noqa: F401

__all__ = ['poly', 'linalg', 'certificates', 'cone', 'quadratic', 'bernstein',
           'univariate', 'recurrence', 'terms', 'induction', 'horn', 'sat',
           'witness', 'io']
__version__ = '0.1.0'
