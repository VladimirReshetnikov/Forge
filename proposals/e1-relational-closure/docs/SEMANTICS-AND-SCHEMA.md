# Semantics and data boundary

The original JSON problem and the evidence are separate arguments. The evidence
cannot choose a new target, program, initial condition, variable order, or domain.
All indices are checked against the original problem.

## Positive certificate

For location l, basis G_l is a list of state polynomials. The checker proves:

1. Every G_l vanishes on every original initial parametrization at l.
2. Every original target p at l is the supplied polynomial combination of G_l.
3. For EVERY original edge e:l->m and EVERY g in G_m, g(F_e(x,u)) is the
   supplied polynomial combination of G_l, with multipliers in state+inputs.

Transition matrices have destination basis rows and source basis columns.
Empty bases and unobserved/unreachable locations are valid when the full
identities justify them. Missing rows or dimensions are rejected.

The checker does NOT require a Groebner-basis proof or an ideal-equality proof:
its final invariant family may be any family satisfying these obligations.

## Negative evidence

Supply an initial branch, exact rational parameter values, a control-compatible
list of edge choices and rational inputs, and an original target index. The
checker computes every intermediate state and accepts only a nonzero original
target at the correct final observation location. Counterexample traces are for
the total rational polynomial IR, not automatically for a source Lean program.

## Polynomial encoding

A polynomial is a sorted list of `[exponent_vector, [numerator, denominator]]`.
The rational entries are canonical decimal strings; denominator > 0, gcd = 1,
no negative zero. Monomial exponents must be nonnegative integers (not booleans).
Duplicate monomials, zero terms, malformed lengths, floats, and nonfinite values
are rejected. Zero polynomial is `[]`.

## Resource boundary

The checker uses independent byte, term, bit-length, exponent, dimension, and
arithmetic-operation limits. It is a research checker, not a hardened untrusted
network service. Supervise it in a resource-limited process for hostile inputs.
The symbolic search has cooperative time checks; the experiment runner also
owns and terminates its worker process. An exhausted budget is UNKNOWN.

The unbounded mathematical termination result does not promise small chains,
small Groebner bases, or a short certificate.
