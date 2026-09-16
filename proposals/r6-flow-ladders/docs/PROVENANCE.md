# Review boundary and provenance

Review date: 15 September 2026.

## Repository pins

- Forge: `c98e47c5f804e92880fc1d0e378c1b95832b685c`.
- Leant: `6bf05ad78c467989e68290f2d08bbed40802d485`.
- Djex: `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`.

The Djex revision is the reviewed main-branch snapshot, not a replacement for
Leant's own dependency pin. Forge's README names Lean v4.34.0 and Mathlib
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`; this environment did not compile them.

## Materials directly reviewed

At the Forge pin:
- README.md
- docs/STATUS.md
- article/sections/07-nonlinear.tex (visible returned chapter content)
- article/sections/B-provenance.tex (visible returned provenance map)
- docs/IDEAS-FROM-LEANT-DJEX.md
- repository tree metadata

At the neighboring pins:
- Leant README, opening and capability-ledger sections.
- Djex README, opening, capability-ledger, and synthesis sections.
- branch metadata establishing their revision identities.

Repository access used the connected GitHub tools. A shell clone attempt failed
because network name resolution was unavailable in the container. A code-search
response for Taylor was marked `incomplete_results: true`; its zero count is not
used as evidence of absence. The review did not read all archived proposals or
the entire merged article end-to-end.

## Novelty scope

The scalar analytic lane, its exact compiler and minimum theorem, positive
systems, and root/point certificates are proposed as a delta against those
reviewed materials. No claim of worldwide mathematical priority or an exhaustive
archive-wide absence audit is made. Existing invariant ideals, closure engines,
polynomial cones, generic trust architecture, and Leant/Djex authority-boundary
ideas are treated as prerequisites, not repackaged as contributions.

Primary-source references, inspected API targets, and related work appear in the
article bibliography. Only the abstract of the Aldaz--Kounchev--Render related
work was inspected; it is cited for context, not as the source of an unverified
technical theorem. The new Python implementation does not copy third-party code.
