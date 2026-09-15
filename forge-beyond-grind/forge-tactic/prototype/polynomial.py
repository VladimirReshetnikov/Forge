"""Exact sparse polynomial arithmetic and a small cone-certificate checker.

The search oracle uses SciPy/HiGHS and SymPy, but verification uses only Fraction
arithmetic. This is a restricted dictionary-SOS / constraint-product search, not
an SDP solver or a complete real-arithmetic decision procedure.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement, product
from typing import Sequence

@dataclass
class Poly:
    n: int
    terms: dict[tuple[int, ...], Q]

    def __post_init__(self):
        if type(self.n) is not int or self.n < 0:
            raise ValueError("nonnegative integral variable count required")
        cleaned = {}
        for m, c in self.terms.items():
            if len(m) != self.n or any(type(k) is not int or k < 0 for k in m):
                raise ValueError("invalid monomial")
            if isinstance(c, float):
                raise ValueError("floating coefficients not allowed")
            c = Q(c)
            if c:
                cleaned[tuple(m)] = c
        self.terms = cleaned

    @staticmethod
    def constant(n, c):
        if isinstance(c, float):
            raise ValueError("floating coefficients not allowed")
        return Poly(n, {(0,) * n: Q(c)})

    @staticmethod
    def mono(m):
        return Poly(len(m), {tuple(m): Q(1)})

    def coerce(self, v):
        if isinstance(v, Poly):
            if v.n != self.n:
                raise ValueError("different variable universes")
            return v
        return Poly.constant(self.n, v)

    def __add__(self, other):
        other = self.coerce(other)
        ts = dict(self.terms)
        for m, c in other.terms.items():
            ts[m] = ts.get(m, Q(0)) + c
        return Poly(self.n, ts)

    __radd__ = __add__

    def __neg__(self):
        return Poly(self.n, {m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        ts = {}
        for a, c in self.terms.items():
            for b, d in other.terms.items():
                m = tuple(x + y for x, y in zip(a, b))
                ts[m] = ts.get(m, Q(0)) + c * d
        return Poly(self.n, ts)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        if type(exponent) is not int or exponent < 0:
            raise ValueError("nonnegative integer exponent required")
        out = Poly.constant(self.n, 1)
        base = self
        while exponent:
            if exponent & 1:
                out = out * base
            base = base * base
            exponent //= 2
        return out

    @property
    def degree(self):
        return max((sum(m) for m in self.terms), default=0)

    def evaluate(self, values):
        if len(values) != self.n:
            raise ValueError("wrong valuation arity")
        return sum((c * _prod(Q(v) ** e for v, e in zip(values, m))
                    for m, c in self.terms.items()), Q(0))

    def encode(self):
        return {"n": self.n,
                "terms": [[list(m), str(c)] for m, c in sorted(self.terms.items())]}

    @staticmethod
    def decode(obj):
        pairs = obj['terms']
        ms = [tuple(m) for m, c in pairs]
        if len(set(ms)) != len(ms):
            raise ValueError("duplicate monomial")
        return Poly(obj['n'], {tuple(m): Q(c) for m, c in pairs})


def _prod(xs):
    out = 1
    for x in xs:
        out *= x
    return out


def variables(n):
    return [Poly.mono(tuple(int(i == j) for i in range(n))) for j in range(n)]


def monomials(n, d):
    if d < 0:
        return []
    return sorted((m for m in product(range(d + 1), repeat=n) if sum(m) <= d),
                  key=lambda m: (sum(m), m))


def check_certificate(target: Poly, gs: Sequence[Poly], hs: Sequence[Poly], cert) -> bool:
    """Prove target >= 0 from gs>=0 and hs=0. No floating-point acceptance."""
    try:
        out = Poly.constant(target.n, 0)
        for item in cert['cone']:
            weight = Q(item['weight'])
            if weight < 0:
                return False
            q = Poly.decode(item['square'])
            term = weight * q * q
            for i in item['factors']:
                if type(i) is not int or not 0 <= i < len(gs):
                    return False
                term = term * gs[i]
            out = out + term
        for item in cert['ideal']:
            i = item['hypothesis']
            if type(i) is not int or not 0 <= i < len(hs):
                return False
            out = out + Poly.decode(item['multiplier']) * hs[i]
        return out.terms == target.terms
    except (ValueError, TypeError, KeyError, ZeroDivisionError):
        return False


def search(target: Poly, gs=(), hs=(), degree=None, products_depth=2,
           max_columns=20000):
    """Return (certificate_or_None, diagnostics). Failure means UNKNOWN.

    Columns are monomial/binomial squares (unconditional), products of supplied
    constraints times monomial squares, and free equality-ideal multiples.
    """
    import numpy as np
    import sympy as sp
    from scipy.optimize import linprog
    n = target.n
    D = degree if degree is not None else max([target.degree] + [g.degree for g in gs] + [h.degree for h in hs])
    columns, metas, bounds = [], [], []
    seen = set()
    def add(p, meta, nonnegative=True):
        if not p.terms:
            return
        key = (tuple(sorted(p.terms.items())), nonnegative)
        if key in seen:
            return
        seen.add(key)
        columns.append(p)
        metas.append(meta)
        bounds.append((0, None) if nonnegative else (None, None))
        if len(columns) > max_columns:
            raise ValueError("dictionary column limit exceeded")
    ms = [Poly.mono(m) for m in monomials(n, D // 2)]
    for q in ms:
        add(q*q, ('cone', q, []))
    for a, b in combinations(ms, 2):
        for sgn in [-1, 1]:
            q = a + sgn*b
            add(q*q, ('cone', q, []))
    for depth in range(1, products_depth + 1):
        for factors in combinations_with_replacement(range(len(gs)), depth):
            gp = Poly.constant(n, 1)
            for i in factors:
                gp = gp * gs[i]
            if gp.degree > D:
                continue
            for m in monomials(n, (D - gp.degree)//2):
                q = Poly.mono(m)
                add(q*q*gp, ('cone', q, list(factors)))
    for i, h in enumerate(hs):
        for m in monomials(n, D - h.degree):
            q = Poly.mono(m)
            add(q*h, ('ideal', q, i), nonnegative=False)
    rows = sorted(set(target.terms).union(*(set(p.terms) for p in columns)))
    if not columns:
        cert = {'cone': [], 'ideal': []}
        return (cert if check_certificate(target, gs, hs, cert) else None,
                {'columns': 0, 'rows': len(rows), 'status': 'empty dictionary'})
    A = np.array([[float(p.terms.get(m, 0)) for p in columns] for m in rows])
    b = np.array([float(target.terms.get(m, 0)) for m in rows])
    cost = np.array([1.0 if bound[0] == 0 else 0.0 for bound in bounds])
    result = linprog(cost, A_eq=A, b_eq=b, bounds=bounds, method='highs',
                     options={'dual_feasibility_tolerance': 1e-9,
                              'primal_feasibility_tolerance': 1e-9})
    diag = {'columns': len(columns), 'rows': len(rows), 'lp_status': int(result.status)}
    if not result.success:
        diag['status'] = 'unknown: no usable LP solution in this dictionary'
        return None, diag
    coeff = [Q(float(x)).limit_denominator(10**6) if abs(x)>1e-8 else Q(0)
             for x in result.x]
    def emit(cs):
        cert = {'cone': [], 'ideal': []}
        for c, (kind, q, data) in zip(cs, metas):
            if not c:
                continue
            if kind == 'cone':
                cert['cone'].append({'weight': str(c), 'square': q.encode(), 'factors': data})
            else:
                cert['ideal'].append({'multiplier': (c*q).encode(), 'hypothesis': data})
        return cert
    cert = emit(coeff)
    if not check_certificate(target, gs, hs, cert):
        support = [i for i, x in enumerate(result.x) if abs(x) > 1e-8]
        mat = sp.Matrix([[sp.Rational(columns[i].terms.get(m, 0)) for i in support] for m in rows])
        rhs = sp.Matrix([sp.Rational(target.terms.get(m, 0)) for m in rows])
        sols = sp.linsolve((mat, rhs))
        if sols is sp.EmptySet or not sols:
            diag['status'] = 'unknown: exact support reconstruction failed'
            return None, diag
        sol = next(iter(sols))
        free = set().union(*(v.free_symbols for v in sol))
        sol = [v.subs({s: 0 for s in free}) for v in sol]
        coeff = [Q(0)]*len(columns)
        for i, v in zip(support, sol):
            coeff[i] = Q(int(v.p), int(v.q))
        cert = emit(coeff)
    if not check_certificate(target, gs, hs, cert):
        diag['status'] = 'unknown: exact checker rejected candidate'
        return None, diag
    diag['status'] = 'certified'
    diag['nonzero_columns'] = len(cert['cone']) + len(cert['ideal'])
    return cert, diag
