"""Anchored analytic certificate search. No floating-point arithmetic is used."""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from math import factorial
from . import algebra as A

@dataclass(frozen=True)
class Jet:
    p: A.Poly
    error: A.Interval


def P(*coefficients: int | Q) -> list:
    return ['poly', A.enc(A.poly(coefficients))]

def plus(a: list, b: list) -> list:
    return ['add', a, b]

def times(a: list, b: list) -> list:
    return ['mul', a, b]

def minus(a: list, b: list) -> list:
    return plus(a, ['neg', b])

def atom(name: str, scale: Q | int = 1) -> list:
    return [name, A.text(scale)]

def coefficient(name: str, a: Q, k: int) -> Q:
    if name == 'exp':
        return a**k / factorial(k)
    if name == 'sin':
        return Q(0) if k % 2 == 0 else (-1)**((k-1)//2)*a**k/factorial(k)
    if name == 'cos':
        return Q(0) if k % 2 else (-1)**(k//2)*a**k/factorial(k)
    if name == 'log1p':
        return Q(0) if k == 0 else (-1)**(k+1)*a**k/k
    if name == 'atan':
        return Q(0) if k % 2 == 0 else (-1)**((k-1)//2)*a**k/k
    raise ValueError('unsupported primitive')

def build(expr: list, b: Q, order: int) -> Jet:
    """Enclose f = p + x^order * r on 0 <= x <= b."""
    op = expr[0]
    if op == 'poly':
        p = A.dec(expr[1])
        return Jet(A.poly(p[:order]), A.horner(A.poly(p[order:]), b))
    if op == 'neg':
        j = build(expr[1], b, order)
        return Jet(A.scale(j.p, -1), (-j.error[1], -j.error[0]))
    if op in ('add', 'mul'):
        f, g = build(expr[1], b, order), build(expr[2], b, order)
        if op == 'add':
            return Jet(A.add(f.p, g.p), A.ia(f.error, g.error))
        full = A.mul(f.p, g.p)
        h = A.poly(full[order:])
        error = A.horner(h, b)
        error = A.ia(error, A.im(A.horner(f.p, b), g.error))
        error = A.ia(error, A.im(A.horner(g.p, b), f.error))
        error = A.ia(error, A.im((Q(0), b**order), A.im(f.error, g.error)))
        return Jet(A.poly(full[:order]), error)
    a = Q(expr[1])
    if op in ('exp', 'sin', 'cos'):
        ratio = abs(a)*b/(order+1)
        if ratio >= 1:
            raise ValueError('exponential majorant ratio is not below one')
        radius = abs(a)**order / factorial(order) / (1-ratio)
    elif op in ('log1p', 'atan'):
        if abs(a)*b >= 1:
            raise ValueError('power-series domain guard failed')
        radius = abs(a)**order / order / (1-abs(a)*b)
    else:
        raise ValueError('unsupported AST node')
    return Jet(A.poly(coefficient(op, a, k) for k in range(order)), (-radius, radius))

def attempt(expr: list, b: Q | int, order: int) -> dict | None:
    b = Q(b)
    if b <= 0 or not 1 <= order <= 40:
        raise ValueError('invalid box/order')
    j = build(expr, b, order)
    m = next((i for i, c in enumerate(j.p) if c), order)
    if m == order:
        bound = j.error
    else:
        bound = A.ia(A.horner(A.poly(j.p[m:]), b),
                     A.im((Q(0), b**(order-m)), j.error))
    if bound[0] < 0:
        return None
    return {'kind': 'anchored', 'subject': {'expr': expr, 'b': A.text(b)},
            'order': order, 'polynomial': A.enc(j.p),
            'error': [A.text(x) for x in j.error], 'valuation': m,
            'margin': A.text(bound[0])}

def search(expr: list, b: Q | int = 1, max_order: int = 24) -> dict | None:
    for order in range(2, min(40, max_order)+1):
        try:
            cert = attempt(expr, b, order)
        except ValueError:
            continue
        if cert is not None:
            return cert
    return None

def unanchored_lower(expr: list, b: Q | int, order: int) -> Q:
    b = Q(b)
    j = build(expr, b, order)
    return A.ia(A.horner(j.p, b), A.im((Q(0), b**order), j.error))[0]
