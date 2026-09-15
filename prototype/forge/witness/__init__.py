"""Witness synthesis families merged from p1, p2, p4, p7 and p9.

  affine      -- p2's Farkas affine witnesses + p1's integral affine mode
  lattice     -- p7's integer lattice / unimodular elimination (verbatim, unique)
  modular     -- p4's finite-residue witnesses (verbatim, unique)
  polynomial  -- p9's polynomial majorant witnesses, retargeted onto forge.cone

Submodules are imported lazily by name; `import forge.witness.lattice` and
`import forge.witness` both work, and only `polynomial` pulls in SciPy/NumPy.
"""
from . import affine, lattice, modular  # noqa: F401  (stdlib-only witnesses)

__all__ = ['affine', 'lattice', 'modular', 'polynomial']
