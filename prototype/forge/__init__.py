"""Forge: one merged prototype assembled from twenty-two independent proposals.

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

The extension round added a family of workers that compute a CLOSURE -- the
smallest invariant object that settles a target -- rather than searching for a
certificate in a fixed language. Five of its lanes are merged here, and all
five are standard library only with their searches included:

  closure.words        e5 + e6 + e9   observable-space closure, separating words
  closure.cover        e8             finite-algebra covers, counterexample trees
  closure.projection   e8             exact one-output integer projection
  closure.kripke       e4             finite Kripke countermodels for IPC
  closure.ore          e9             common left multiples, singularity plans

The ideal-closure and telescoping lanes are not merged: their searches need a
Groebner engine and exact bivariate nullspaces respectively, so they cannot be
standard library only. Run those from proposals/e1, e3, e6, e7 and e9.

The fourth round added workers that return a FINITE BASIS for an infinite set
of states, so that one certificate settles infinitely many instances by
comparison rather than by search. Its largest cluster is merged here:

  wsts.orders        s1 + s3 + s4   Dickson and Higman orders, one antichain
  wsts.nets          s1 + s3 + s4   nets, counter systems, matrix updates,
                                    lossy FIFO channels
  wsts.summaries     s1             compressed runs and a hash-consed run DAG
  wsts.search        s1 + s3 + s4   one backward loop, four predecessor rules
  wsts.certificates  s1 + s3 + s4   every checker, no search code

Four proposals wrote that order, antichain, predecessor formula and saturation
loop three or four times between them. Each appears once here. The rest of the
fourth round is not merged: see forge/wsts/__init__.py for which, and why.

The third round is not merged at all. Its noncommutative, analytic and
quantitative lanes need a noncommutative Groebner engine, interval arithmetic
over transcendental constants, and exact linear programming respectively. Run
them from proposals/r1..r9.
"""
from . import (poly, linalg, certificates, cone, quadratic, bernstein, univariate,
               recurrence, terms, induction, horn, sat, witness, io,
               closure, wsts)  # noqa: F401

__all__ = ['poly', 'linalg', 'certificates', 'cone', 'quadratic', 'bernstein',
           'univariate', 'recurrence', 'terms', 'induction', 'horn', 'sat',
           'witness', 'io', 'closure', 'wsts']
__version__ = '0.1.0'
