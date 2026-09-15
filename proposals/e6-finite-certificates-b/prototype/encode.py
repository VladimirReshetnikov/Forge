"""Search-side encoding. The independent checker never imports this file."""
from __future__ import annotations
import sympy as s

def rational(x):
    x = s.Rational(x)
    return [int(x.p), int(x.q)]

def polynomial(x, variables):
    x = s.expand(x)
    if not variables:
        return [] if x == 0 else [[[], rational(x)]]
    p = s.Poly(x, *variables, domain=s.QQ)
    return [[list(e), rational(c)] for e,c in sorted(p.terms()) if c]

def vector(x):
    return [rational(v) for v in x]

def matrix(x):
    return [vector(list(x.row(i))) for i in range(x.rows)]
