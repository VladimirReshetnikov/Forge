"""Finite certificates for unbounded behaviour: the extension round's workers.

PROVENANCE
  words       e5 + e6 + e9   target-directed observable-space closure over a
                             finite alphabet; separating words; the D-1 bound
  cover       e8             finite-algebra covers and counterexample trees
  projection  e8             exact one-output integer projection with Bezout
                             receipts and a straight-line witness program
  kripke      e4             finite Kripke countermodels for IPC
  ore         e9             common-left-multiple certificates, singularity
                             seed plans, complete natural-root covers
  certificates                every checker in this subpackage, no search code

Not merged here, and deliberately:

  Target-generated ideal closure (e1, e3, e6, e7) needs a Groebner engine, so
  its search cannot be standard-library-only. Its checker could be; the
  existing forge.recurrence and forge.certificates already cover the shapes
  the merged corpus exercises. Run it from proposals/e1/, proposals/e3/,
  proposals/e6/ or proposals/e7/.

  Boundary-safe telescoping (e2, e3, e6, e9) needs exact bivariate nullspaces.
  The same applies. Run it from proposals/e9/, which has the widest fragment.

Everything in this subpackage is standard library only, search included, so the
whole of it runs under `python -S`. That is a property of these five lanes, not
a claim about the others.
"""
from . import words, cover, projection, kripke, ore, certificates  # noqa: F401

__all__ = ['words', 'cover', 'projection', 'kripke', 'ore', 'certificates']
