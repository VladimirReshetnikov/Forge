/-
  Forge: generated certificate replays and illustrative specimens.

  COMPILED, file by file: every Mathlib-dependent file below compiles on the
  pinned toolchain against the pinned Mathlib, with no errors and no `sorry`
  (tools/build_mathlib_forge.py, results/lean-mathlib-forge.json), and
  lean/MathlibAudit.lean checks their theorems' axioms. No proposal in this
  project had a Lean toolchain available; none of this was compiled when merged.

  Nothing here implements a `forge` tactic. `Forge/Design/` contains proposed
  data contracts, `Forge/Generated/` contains proof scripts emitted by the
  Python prototypes, and `Forge/Examples/` contains hand-written specimens
  showing the proof shapes the design targets.
-/
import Forge.Design.Runtime
import Forge.Design.Contracts

import Forge.Closure.Principles
import Forge.Closure.Covers
import Forge.Closure.Indexing

import Forge.Generated.SOS
import Forge.Generated.SOSExtra
import Forge.Generated.Bernstein
import Forge.Generated.Induction
import Forge.Generated.Invariants
import Forge.Generated.Witnesses

import Forge.Examples.Structural
import Forge.Examples.Basic
import Forge.Examples.Arithmetic
import Forge.Examples.CrossTheory
import Forge.Examples.Lattice
import Forge.Examples.Residue
import Forge.Examples.Accumulator
import Forge.Examples.Mixed
