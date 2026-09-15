"""Synthesis and exact replay for one explicitly bounded induction template.

run([], a) = a; run(h::t,a) = run(t, r*a+w*h+c).
Template: run(xs,a) = A*a+B*sum(xs)+C*len(xs)+D.
No general induction prover is claimed. Replay checks the two universally
quantified polynomial obligations that justify an ordinary list induction.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from poly import Poly, rational

@dataclass(frozen=True)
class Certificate:
    A: Q
    B: Q
    C: Q
    D: Q


def replay(r: Q, w: Q, c: Q, cert: Certificate) -> bool:
    try:
        r,w,c = rational(r), rational(w), rational(c)
        if not all(isinstance(v,Q) for v in (cert.A,cert.B,cert.C,cert.D)):
            return False
        a,h,s,l = (Poly.var(4,j) for j in range(4))
        A,B,C,D = cert.A,cert.B,cert.C,cert.D
        base = a - (A*a+D)
        step = A*(r*a+w*h+c)+B*s+C*l+D - (A*a+B*(h+s)+C*(l+1)+D)
        return not base.terms and not step.terms
    except (ValueError, TypeError, AttributeError):
        return False


def search(r: Q, w: Q, c: Q) -> Certificate | None:
    """Linear synthesis over coefficients, followed by independent replay."""
    import sympy as sp
    r,w,c = rational(r), rational(w), rational(c)
    def S(x): return sp.Rational(x.numerator,x.denominator)
    A,B,C,D = sp.symbols('A B C D')
    sol = sp.linsolve([A-1, D, A*(S(r)-1), A*S(w)-B, A*S(c)-C], (A,B,C,D))
    if sol == sp.EmptySet:
        return None
    values = next(iter(sol))
    if any(v.free_symbols for v in values):
        return None
    cert = Certificate(*(Q(int(v.p),int(v.q)) for v in values))
    return cert if replay(r,w,c,cert) else None


def run(xs: list[int], a: int, r: int, w: int, c: int) -> int:
    for h in xs:
        a = r*a+w*h+c
    return a
