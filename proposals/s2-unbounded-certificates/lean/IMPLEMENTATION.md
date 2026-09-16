# Lean port: obligations, not an uncompiled implementation claim

**Status: NOT_RUN.** No Lean/lake executable was available in this authoring environment, and attempted toolchain acquisition failed. This directory deliberately contains no `sorry`-based or uncompiled theorem file presented as a completed implementation.

Forge already has core-only files that its merge compiled. This status concerns this extension only.

## First vertical slice: Petri safety

Proposed files, relative to `Forge/Unbounded/`:

1. `PetriModel.lean`: `Fin d -> Nat` markings, input/output transitions, guarded firing, upward closure, finite execution relation.
2. `PetriCheck.lean`: decode the basis and coverage indices; check exact coordinate inequalities; prove that the complement of the basis's upward closure is preserved by firing.
3. `PetriSource.lean`: a small resource DSL and its forward simulation into the net.
4. `Examples/Mutex.lean`: prove the original source program never has two owners using the delivered three-element basis. Also replay a concrete violation of a deliberately broken sibling.

The predecessor lemma is:

    pre + max(0, bad - post) <= marking
    iff enabled and fired_marking >= bad.

Interpret subtraction carefully. In Lean natural-number code, retaining the enabling hypothesis is mandatory when relating truncated subtraction to integer rearrangement.

The checker needs neither Dickson's lemma nor a minimality proof. Those are later requirements for the search-completeness theorem, not for the accepted invariant.

## Second slice: inverse-free lower bounds

1. `PPSModel.lean`: sparse rational coefficients and exponent vectors; validity, evaluation and casts to real-valued functions.
2. `PPSLfp.lean`: monotone map on a complete-lattice unit cube, least fixed point, prefixed upper bounds; separately prove agreement with iterates from zero.
3. `WeightedStep.lean`: nonnegative monomial expansion and the finite weighted maximum principle.
4. `EnclosureCheck.lean`: induction over lower steps, exact upper check, requested-width result.

For a lower point l already known <= q, check:

    w > 0
    d >= 0
    J(l) w < w           -- strict in EVERY coordinate
    (I - J(l)) d <= P(l) - l
    l <= next <= l + d

The proof does not require matrix inversion. If `(I-J)z >= 0`, a negative minimum of `z_i/w_i` contradicts `Jw<w`. Applying this to `z=q-l-d` proves the step.

Do not round d independently and assume its residual inequality remains true: `I-J` has negative off-diagonal entries. Round only `next`, or recheck the residual of a new d.

Essential negative fixtures: forged larger fixed point for `P(x)=1/4+3/4*x^3`; nonstrict weight on `P(x)=x`; invalid dimensions, subject or width; upward rounding beyond the exact lower-step limit.

## Exact special cases

`ExtinctionCheck.lean` must prove the mean-weight theorem with normalization, strong connectivity, and nondegeneracy. `P(x)=(1+x*x)/2` must be accepted; `P(x)=x` must not.

`RootDecode.lean` must prove interval Horner soundness, polynomial factor identity transport, and uniqueness from a strict derivative sign. The initial target is the exact root `(sqrt 21 - 3)/6`, not a decimal approximation.

## Semantic source bridge

A stochastic grammar rule is an exact rational probability plus a finite list of independent recursive child types. Compile child multiplicities into a monomial. Prove that source finite-height success probabilities equal polynomial iterates from zero. The limiting probability is then the least fixed point.

Shared randomness, mutable state, and unbounded data-dependent procedure parameters are not automatically supported. Neither typed term reconstruction nor polynomial parsing proves independence.

## Acceptance gates

- Compile every delivered Lean module against the chosen Lean/Mathlib revision.
- Prove checker soundness, not merely evaluate Boolean checks.
- Replay both valid and invalid stored certificates through the actual decoder.
- Prove at least one theorem about original source semantics, not only an abstract model.
- Print and inspect the actual axiom inventory.
- Recompile the final proof without invoking search.
- Measure checker time/term size and separate source extraction from search and reconstruction.

Mathlib API names in the article were checked in current documentation, not compiled against Forge's pin. Confirm the chosen revision's imports before implementing the port.
