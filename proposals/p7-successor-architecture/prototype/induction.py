"""Generalized accumulator invariants synthesized and checked exactly.

Input: polynomial r(n) and recursive equations
  go(0,a) = a
  go(n+1,a) = go(n,a+r(n)).
The desired go(n,0) is strengthened to go(n,a)=F(n,a). Exact base and step
identities justify an ordinary structural-induction proof. This is an
object-language experiment, not a Lean elaborator or a generic induction tactic.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from polynomial import Poly, exact_linear_solve

@dataclass(frozen=True)
class Certificate:
    invariant: Poly
    generalized: tuple[str, ...] = ('a',)

    def json(self):
        return {'invariant': self.invariant.json(), 'generalized': list(self.generalized)}


def changed_nonstructural_parameters(formals: tuple[str, ...],
                                     actuals: tuple[Poly, ...],
                                     structural: set[int]) -> tuple[str, ...]:
    if len(formals) != len(actuals): raise ValueError('arity mismatch')
    return tuple(name for i, (name, actual) in enumerate(zip(formals, actuals))
                 if i not in structural and actual != Poly.var(len(formals), i))


def check(r: Poly, cert: Certificate) -> bool:
    """Universal polynomial identities, no finite-sample acceptance."""
    if r.n != 2 or cert.invariant.n != 2: return False
    if any(m[1] for m, _ in r.terms): return False
    n, a = Poly.var(2, 0), Poly.var(2, 1)
    F = cert.invariant
    base = F.substitute([Poly.const(2), a])
    step_lhs = F.substitute([n+1, a])
    step_rhs = F.substitute([n, a+r])
    return base == a and step_lhs == step_rhs


def synthesize(r: Poly, max_degree: int = 10, generalize: bool = True):
    """Find least tried degree in F(n,a)=P(n)+a Q(n) by rational RREF."""
    if r.n != 2 or any(m[1] for m, _ in r.terms):
        raise ValueError('r must be a polynomial in variable n only')
    n, a = Poly.var(2, 0), Poly.var(2, 1)
    generalized = changed_nonstructural_parameters(('n', 'a'), (n, a+r), {0})
    for degree in range(1, max_degree+1):
        basis = [n**k for k in range(degree+1)]
        if generalize: basis += [a*n**k for k in range(degree)]
        # Encode both equations in a disjoint polynomial block using a third var.
        def lift(p):
            return Poly.make(3, {(m[0], m[1], 0): c for m, c in p.terms})
        tag = Poly.var(3, 2)
        cols = [lift(p.substitute([Poly.const(2), a])) + tag*lift(
            p.substitute([n+1, a])-p.substitute([n, a+r])) for p in basis]
        coeffs = exact_linear_solve(cols, lift(a))
        if coeffs is None: continue
        F = sum((c*p for c, p in zip(coeffs, basis)), Poly.const(2))
        cert = Certificate(F, generalized)
        if check(r, cert):
            return cert, {'degree': degree, 'unknowns': len(basis),
                          'generalized': list(generalized)}
    return None, {'max_degree': max_degree, 'generalized': list(generalized)}


def execute(r: Poly, n: int, a: int | Q):
    if n < 0: raise ValueError('natural structural parameter required')
    acc = Q(a)
    while n:
        n -= 1
        acc += r.evaluate([n, 0])
    return acc
