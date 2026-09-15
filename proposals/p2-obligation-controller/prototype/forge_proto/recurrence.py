"""Counterexample-guided polynomial invariants for additive recurrences.

Input: T(0)=initial, T(n+1)=T(n)+increment(n), n in N, rational values.
Output: exact polynomial Q with independent base/step certificate checking.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction as Q
from .poly import Poly
from .linear import solve_exact


@dataclass
class RecurrenceResult:
    polynomial: Poly | None
    candidates: int = 0
    counterexamples: list[dict] = field(default_factory=list)
    inconsistent_degrees: list[int] = field(default_factory=list)


def check_recurrence(increment: Poly, initial: Q, candidate: Poly) -> bool:
    if increment.n != 1 or candidate.n != 1:
        return False
    x = Poly.variable(1, 0)
    return (candidate.evaluate([0]) == Q(initial)
            and candidate.substitute([x + 1]) - candidate == increment)


def synthesize_recurrence(increment: Poly, initial: Q = Q(0), max_degree: int = 8) -> RecurrenceResult:
    if increment.n != 1 or max_degree < 0:
        raise ValueError("univariate increment and nonnegative degree bound required")
    samples = {0: Q(initial)}
    values = [Q(initial)]
    result = RecurrenceResult(None)

    def at(n: int) -> Q:
        while len(values) <= n:
            k = len(values) - 1
            values.append(values[-1] + increment.evaluate([k]))
        return values[n]

    x = Poly.variable(1, 0)
    for degree in range(max_degree + 1):
        while True:
            coefficients = solve_exact([[Q(n) ** k for k in range(degree + 1)]
                                        for n in sorted(samples)],
                                       [samples[n] for n in sorted(samples)], degree + 1)
            if coefficients is None:
                result.inconsistent_degrees.append(degree)
                break
            candidate = Poly.make(1, [((k,), c) for k, c in enumerate(coefficients)])
            result.candidates += 1
            if check_recurrence(increment, initial, candidate):
                result.polynomial = candidate
                return result
            residual = candidate.substitute([x + 1]) - candidate - increment
            # A nonzero degree-d polynomial cannot vanish at d+1 distinct points.
            bad = next(n for n in range(residual.total_degree() + 1)
                       if residual.evaluate([n]))
            result.counterexamples.append({"degree": degree, "n": bad,
                                           "candidate": candidate.to_json(),
                                           "step_residual": str(residual.evaluate([bad]))})
            samples[bad] = at(bad)
            samples[bad + 1] = at(bad + 1)
    return result
