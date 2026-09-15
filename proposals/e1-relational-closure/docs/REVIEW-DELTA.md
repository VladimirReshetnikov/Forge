# Reviewed source and non-duplication boundary

The new proposal does not re-present Forge's global obligation graph,
certificate-first policy, induction generalization, theorem retrieval, SAT/Horn
workers, SOS/Bernstein/Sturm algorithms, LJT negative-evidence proposal, neutral
IR, provider provenance, or fair scheduling as new contributions.

Reviewed Forge source at `674521027d968d59f7b83220ed52304a85cb55e2`:

- README and the recursive repository/module inventory.
- `docs/IDEAS-FROM-LEANT-DJEX.md`.
- `article/sections/03-architecture.tex` (first 260 lines).
- `article/sections/05-structural.tex` (targeted windows covering backward
  matching, induction, recurrence synthesis, multi-invariant discussion,
  negative evidence, and witness synthesis; long responses were bounded).
- `article/sections/06-nonlinear.tex` (first 240 lines).
- `article/sections/08-integration.tex` (first 240 lines).
- `prototype/forge/recurrence.py`.

This was a focused source review, not an exhaustive line-by-line review of all
nine frozen submissions. Search absence is not treated as proof of novelty.

The decisive delta is that the reviewed structural chapter ALREADY writes the
multi-invariant equation `I_i(T(x)) = sum_j h_ij(x) I_j(x)` and notes the bilinear
problem if I and h are unknown together. The new worker constructs a concrete
finite invariant family by target pullbacks and ideal growth, then constructs
multipliers for that fixed family. Merely repeating the displayed equation
would not be an addition.

Leant/Djex review used their READMEs and Leant's
`docs/behavioral-synthesis.md`. The latter's actual `decide`/bounded `simp`
assertion-discharge contract motivates a NEW supported universal polynomial-fold
lane. No claim is made to solve the original integer-indexing or simultaneous
two-universe composition gaps in those projects.

Full source URLs and primary mathematical literature appear in the article.
