# Repository-relative scope

Reviewed canonical Forge at `c98e47c5f804e92880fc1d0e378c1b95832b685c`:
README, implementation status, Leant/Djex review, provenance appendix,
conclusion, logical certificate contract, and recursive repository tree.

The canonical inventory already includes induction/generalization, arithmetic
witnesses, nonlinear cones/Bernstein/Sturm, Horn/CDCL, observable closure, ideal
closure, finite-algebra covers, exact integer projection, Kripke countermodels,
continuation-local synthesis, cyclic descent, telescoping, and Ore transport.
Those are prerequisites, not additions in this proposal.

The four additions concern distinct semantics: infinite adversarial parity
objectives; prescribed-marginal probability coupling and optimal defect;
alternating source/target action matching under probabilistic transitions;
and universal-scheduler expected termination despite graph cycles.

This is a comparison with the merged canonical design and capability inventory,
not a claim to have exhaustively scanned every line of all eighteen preserved
submissions. Leant and Djex were consulted for their currently documented
source-owned synthesis surfaces, not re-audited implementation-wide.

Forge's merge records successful elaboration of sixteen core-only Lean files.
It would be inaccurate to describe the current repository as having no Lean
compilation evidence. Its canonical status still does not claim an implemented
Forge tactic or formally verified certificate checkers. The new archive likewise
does not claim to close that gap.

The full paper gives separate mathematical arguments for each checker, but the
executed evidence is Python evidence. The next end-to-end gate is an actual
source distribution theorem via rational marginal checking and a PMF bridge.
