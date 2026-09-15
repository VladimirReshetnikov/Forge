"""Recurrence / accumulator invariant synthesis, checked by universal identities.

PROVENANCE
  BASE  p1-structural-search/prototype/forge/synthesis.py::synthesize_recurrence
        (multivariate, exact: a single rational RREF over a monomial basis).
  FOLD  p2-obligation-controller/prototype/forge_proto/recurrence.py -- its CEGIS
        counterexample loop, kept as an OPTIONAL diagnostic mode; it reports the
        first n where a proposed closed form fails, and is never an acceptance
        path of its own.
  FOLD  p7-successor-architecture/prototype/induction.py -- the tag-variable
        block-lifting trick (two identities solved as one linear system in a
        disjoint polynomial block) and changed_nonstructural_parameters.
  FOLD  p5-certificate-first/prototype/forge/invariants.py -- InvariantCertificate
        (from certificates.py) as the persisted format; p5 proposed Q by SymPy
        interpolation, this does it exactly, so no SymPy is needed at all.

Sampling and interpolation only ever REJECT candidates. Acceptance is always an
exact polynomial identity.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction as Q
from typing import Sequence
from .poly import Poly, monomial_exponents
from .linalg import solve_linear, exact_linear_solve
from .certificates import InvariantCertificate, check_invariant


# ---------------------------------------------------------------------------
# p1: multivariate additive recurrences  F(0,a)=initial(a),  F(n+1,a)-F(n,a)=step
# ---------------------------------------------------------------------------
def check_recurrence(step: Poly, initial: Poly, formula: Poly) -> bool:
    """Check F(0,a)=initial(a) and F(n+1,a)-F(n,a)=step(n,a)."""
    try:
        if not step.n == initial.n == formula.n:
            return False
        if any(e[0] for e, _ in initial.terms):
            return False
        variables = [Poly.var(step.n, i) for i in range(step.n)]
        shifted = [variables[0] + 1, *variables[1:]]
        at_zero = [Poly.const(step.n, 0), *variables[1:]]
        return (formula.substitute(at_zero) == initial and
                formula.substitute(shifted) - formula == step)
    except (ValueError, TypeError, AttributeError):
        return False


def synthesize_recurrence(step: Poly, initial: Poly, max_degree: int = 8) -> Poly | None:
    if step.n != initial.n or any(e[0] for e, _ in initial.terms):
        raise ValueError('initial value must not depend on recurrence index')
    if max_degree < 0:
        raise ValueError('negative degree budget')
    variables = [Poly.var(step.n, i) for i in range(step.n)]
    shifted = [variables[0] + 1, *variables[1:]]
    at_zero = [Poly.const(step.n, 0), *variables[1:]]
    for degree in range(max_degree + 1):
        basis = [Poly.monomial(step.n, e) for e in monomial_exponents(step.n, degree)]
        deltas = [q.substitute(shifted) - q for q in basis]
        bases = [q.substitute(at_zero) for q in basis]
        support_step = sorted(set(e for q in [step, *deltas] for e, _ in q.terms))
        support_base = sorted(set(e for q in [initial, *bases] for e, _ in q.terms))
        ds, bs = [dict(q.terms) for q in deltas], [dict(q.terms) for q in bases]
        sd, bd = dict(step.terms), dict(initial.terms)
        a = [[d.get(e, 0) for d in ds] for e in support_step]
        a += [[d.get(e, 0) for d in bs] for e in support_base]
        b = [sd.get(e, 0) for e in support_step] + [bd.get(e, 0) for e in support_base]
        coefficients = solve_linear(a, b, len(basis))
        if coefficients is not None:
            formula = sum((c * q for c, q in zip(coefficients, basis)),
                          Poly.const(step.n, 0))
            if check_recurrence(step, initial, formula):
                return formula
    return None


# ---------------------------------------------------------------------------
# p2: CEGIS diagnostic mode (univariate). Sampling proposes; identities accept.
# ---------------------------------------------------------------------------
@dataclass
class RecurrenceResult:
    polynomial: Poly | None
    candidates: int = 0
    counterexamples: list[dict] = field(default_factory=list)
    inconsistent_degrees: list[int] = field(default_factory=list)


def check_univariate_recurrence(increment: Poly, initial: Q, candidate: Poly) -> bool:
    if increment.n != 1 or candidate.n != 1:
        return False
    x = Poly.var(1, 0)
    return (candidate.evaluate([0]) == Q(initial)
            and candidate.substitute([x + 1]) - candidate == increment)


def synthesize_recurrence_cegis(increment: Poly, initial: Q = Q(0),
                                max_degree: int = 8) -> RecurrenceResult:
    """Counterexample-guided variant, reported for diagnostics only.

    Agreement with a finite sample table never certifies anything: the returned
    polynomial is accepted only by check_univariate_recurrence.
    """
    if increment.n != 1 or max_degree < 0:
        raise ValueError('univariate increment and nonnegative degree bound required')
    samples = {0: Q(initial)}
    values = [Q(initial)]
    result = RecurrenceResult(None)

    def at(n: int) -> Q:
        while len(values) <= n:
            values.append(values[-1] + increment.evaluate([len(values) - 1]))
        return values[n]

    x = Poly.var(1, 0)
    for degree in range(max_degree + 1):
        while True:
            coefficients = solve_linear([[Q(n) ** k for k in range(degree + 1)]
                                         for n in sorted(samples)],
                                        [samples[n] for n in sorted(samples)],
                                        degree + 1)
            if coefficients is None:
                result.inconsistent_degrees.append(degree)
                break
            candidate = Poly.make(1, [((k,), c) for k, c in enumerate(coefficients)])
            result.candidates += 1
            if check_univariate_recurrence(increment, initial, candidate):
                result.polynomial = candidate
                return result
            residual = candidate.substitute([x + 1]) - candidate - increment
            # A nonzero degree-d polynomial cannot vanish at d+1 distinct points.
            bad = next(n for n in range(residual.degree + 1) if residual.evaluate([n]))
            result.counterexamples.append({'degree': degree, 'n': bad,
                                           'candidate': candidate.json(),
                                           'step_residual': str(residual.evaluate([bad]))})
            samples[bad] = at(bad)
            samples[bad + 1] = at(bad + 1)
    return result


# ---------------------------------------------------------------------------
# p7: accumulator generalisation  go(0,a)=a,  go(n+1,a)=go(n, a+r(n)).
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class AccumulatorCertificate:
    invariant: Poly
    generalized: tuple[str, ...] = ('a',)

    def json(self) -> dict:
        return {'invariant': self.invariant.json(), 'generalized': list(self.generalized)}


def changed_nonstructural_parameters(formals: Sequence[str], actuals: Sequence[Poly],
                                     structural: set[int]) -> tuple[str, ...]:
    if len(formals) != len(actuals):
        raise ValueError('arity mismatch')
    return tuple(name for i, (name, actual) in enumerate(zip(formals, actuals))
                 if i not in structural and actual != Poly.var(len(formals), i))


def check_accumulator(r: Poly, cert: AccumulatorCertificate) -> bool:
    """Universal polynomial identities, no finite-sample acceptance."""
    try:
        if r.n != 2 or cert.invariant.n != 2:
            return False
        if any(m[1] for m, _ in r.terms):
            return False
        n, a = Poly.var(2, 0), Poly.var(2, 1)
        F = cert.invariant
        return (F.substitute([Poly.const(2, 0), a]) == a and
                F.substitute([n + 1, a]) == F.substitute([n, a + r]))
    except (ValueError, TypeError, AttributeError):
        return False


def synthesize_accumulator(r: Poly, max_degree: int = 10, generalize: bool = True):
    """Find the least degree with F(n,a) = P(n) + a*Q(n) by rational RREF (p7)."""
    if r.n != 2 or any(m[1] for m, _ in r.terms):
        raise ValueError('r must be a polynomial in the index variable only')
    n, a = Poly.var(2, 0), Poly.var(2, 1)
    generalized = changed_nonstructural_parameters(('n', 'a'), (n, a + r), {0})
    for degree in range(1, max_degree + 1):
        basis = [n ** k for k in range(degree + 1)]
        if generalize:
            basis += [a * n ** k for k in range(degree)]

        # Encode both equations in a disjoint polynomial block using a third
        # tag variable, so one RREF solves the base and step obligations at once.
        def lift(p: Poly) -> Poly:
            return Poly.make(3, {(m[0], m[1], 0): c for m, c in p.terms})

        tag = Poly.var(3, 2)
        cols = [lift(p.substitute([Poly.const(2, 0), a]))
                + tag * lift(p.substitute([n + 1, a]) - p.substitute([n, a + r]))
                for p in basis]
        coeffs = exact_linear_solve(cols, lift(a))
        if coeffs is None:
            continue
        F = sum((c * p for c, p in zip(coeffs, basis)), Poly.const(2, 0))
        cert = AccumulatorCertificate(F, generalized)
        if check_accumulator(r, cert):
            return cert, {'degree': degree, 'unknowns': len(basis),
                          'generalized': list(generalized)}
    return None, {'max_degree': max_degree, 'generalized': list(generalized)}


def run_accumulator(r: Poly, n: int, a: int | Q) -> Q:
    """Reference interpreter for the accumulator recursion (p7)."""
    if type(n) is not int or n < 0:
        raise ValueError('natural structural parameter required')
    acc = Q(a)
    while n:
        n -= 1
        acc += r.evaluate([n, 0])
    return acc


# ---------------------------------------------------------------------------
# p5: the persisted format is InvariantCertificate(invariant, initial, transition)
# ---------------------------------------------------------------------------
def additive_invariant(increment: Poly, *, initial: Q = Q(0),
                       degree: int | None = None) -> InvariantCertificate | None:
    """For n' = n+1, s' = s + p(n), synthesize the invariant I(n,s) = s - Q(n).

    p5 proposed Q by SymPy interpolation over a finite table; here Q comes from
    the exact RREF above, so the whole path is stdlib-only. Acceptance still
    depends exclusively on check_invariant's two exact identities.
    """
    if increment.n != 1:
        raise ValueError('increment must be univariate')
    degree = increment.degree + 1 if degree is None else degree
    if degree < 0:
        raise ValueError('invalid degree')
    lifted = Poly.make(2, {(m[0], 0): c for m, c in increment.terms})
    q = synthesize_recurrence(lifted, Poly.const(2, Q(initial)), degree)
    if q is None:
        return None
    nv, sv = Poly.var(2, 0), Poly.var(2, 1)
    cert = InvariantCertificate(sv - q, (Q(0), Q(initial)), (nv + 1, sv + lifted))
    return cert if check_invariant(cert) else None
