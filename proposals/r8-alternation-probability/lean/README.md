# Lean status: NOT_RUN

These two proof-script specimens were written but **not compiled**. No Lean
executable was available in the authoring runtime. No kernel acceptance or axiom
inventory is claimed. The `#print axioms` commands are pending executions, not
records of output.

- `RankTelescoping.lean`: arithmetic prefix-sum lemma used after a parity play
  enters a threshold tail. It is not an infinite-play theorem or game checker.
- `CouplingAlgebra.lean`: finite rational marginal identities. It is not the
  transport certificate checker, Hall optimality theorem, or PMF source bridge.

The intended context follows Forge: Lean v4.34.0 and Mathlib commit
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`.

From a configured project, run `lake env lean path/to/RankTelescoping.lean` and
`lake env lean path/to/CouplingAlgebra.lean`. Compilation, repairs if needed,
and a recorded axiom audit are mandatory before describing either as checked.
The article's source-reification and worker integration steps remain separate.
