"""Exact real algebraic arithmetic for the two-variable atlas checker.

Standard library only. Polynomials are dense, low-degree coefficient first.
An algebraic base point is a square-free rational polynomial plus one isolated
real root. Coefficients at that point are localized rational functions; the
quotient by a possibly reducible defining polynomial is NOT assumed a field.
This research implementation is not formally verified or hostile-input hardened.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Any, Iterable

class LimitExceeded(RuntimeError):
    """A configured arithmetic/refinement bound was reached: no verdict."""

MAX_REFINEMENTS = 512
MAX_ISOLATION_NODES = 20000


def sign(a: Any) -> int:
    if isinstance(a, AElem):
        return a.sign()
    return (a > 0) - (a < 0)


def trim(p: Iterable[Any]) -> tuple:
    a = list(p)
    while a and a[-1] == 0:
        a.pop()
    return tuple(a)


def add(p: tuple, q: tuple) -> tuple:
    return trim((p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
                for i in range(max(len(p), len(q))))


def neg(p: tuple) -> tuple:
    return tuple(-a for a in p)


def sub(p: tuple, q: tuple) -> tuple:
    return add(p, neg(q))


def scale(p: tuple, a: Any) -> tuple:
    return trim(c * a for c in p)


def mul(p: tuple, q: tuple) -> tuple:
    if not p or not q:
        return ()
    a = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            a[i + j] += x * y
    return trim(a)


def power(p: tuple, n: int) -> tuple:
    if type(n) is not int or n < 0:
        raise ValueError('nonnegative exponent required')
    r = (Q(1),)
    while n:
        if n & 1:
            r = mul(r, p)
        p = mul(p, p)
        n //= 2
    return r


def divmod_poly(p: tuple, q: tuple) -> tuple[tuple, tuple]:
    if not q:
        raise ZeroDivisionError('zero polynomial divisor')
    r = list(p)
    ans = [0] * max(0, len(p) - len(q) + 1)
    while len(r) >= len(q):
        k = len(r) - len(q)
        c = r[-1] / q[-1]
        ans[k] += c
        for i, a in enumerate(q):
            r[k + i] -= c * a
        r = list(trim(r))
    return trim(ans), tuple(r)


def quotient(p: tuple, q: tuple) -> tuple:
    a, b = divmod_poly(p, q)
    if b:
        raise ArithmeticError('nonexact polynomial division')
    return a


def monic(p: tuple) -> tuple:
    return scale(p, 1 / p[-1]) if p else ()


def gcd(p: tuple, q: tuple) -> tuple:
    while q:
        p, q = q, divmod_poly(p, q)[1]
    return monic(p)


def derivative(p: tuple) -> tuple:
    return trim(i * p[i] for i in range(1, len(p)))


def squarefree(p: tuple) -> tuple:
    if len(p) <= 1:
        return (Q(1),)
    return monic(quotient(p, gcd(p, derivative(p))))


def evaluate(p: tuple, x: Any) -> Any:
    r: Any = 0
    for a in reversed(p):
        r = r * x + a
    return r


def variations(signs: Iterable[int]) -> int:
    nonzero = [s for s in signs if s]
    return sum(a != b for a, b in zip(nonzero, nonzero[1:]))


def sturm(p: tuple) -> tuple[tuple, ...]:
    """Signed Euclidean remainder chain. p must be nonzero."""
    if not p:
        raise ValueError('Sturm chain of zero polynomial')
    out = [p]
    d = derivative(p)
    if d:
        out.append(d)
    while len(out) > 1:
        r = neg(divmod_poly(out[-2], out[-1])[1])
        if not r:
            break
        out.append(r)
    return tuple(out)


def at_infinity(p: tuple, positive: bool) -> int:
    s = sign(p[-1])
    return s if positive or (len(p) - 1) % 2 == 0 else -s


def total_roots(chain: tuple[tuple, ...]) -> int:
    return (variations(at_infinity(p, False) for p in chain)
            - variations(at_infinity(p, True) for p in chain))


def root_count(chain: tuple[tuple, ...], lo: Q, hi: Q) -> int:
    """Count roots in (lo, hi); endpoints must not be roots of chain[0]."""
    if not lo < hi:
        raise ValueError('empty/reversed root interval')
    if evaluate(chain[0], lo) == 0 or evaluate(chain[0], hi) == 0:
        raise ValueError('root at an interval endpoint')
    return (variations(sign(evaluate(p, lo)) for p in chain)
            - variations(sign(evaluate(p, hi)) for p in chain))


def iadd(a: tuple[Q, Q], b: tuple[Q, Q]) -> tuple[Q, Q]:
    return a[0] + b[0], a[1] + b[1]


def imul(a: tuple[Q, Q], b: tuple[Q, Q]) -> tuple[Q, Q]:
    v = [x * y for x in a for y in b]
    return min(v), max(v)


def idiv(a: tuple[Q, Q], b: tuple[Q, Q]) -> tuple[Q, Q]:
    if b[0] <= 0 <= b[1]:
        raise ZeroDivisionError('interval includes zero')
    return imul(a, (1 / b[1], 1 / b[0]))


def interval(a: Any) -> tuple[Q, Q]:
    if isinstance(a, AElem):
        return a.interval()
    return Q(a), Q(a)


def interval_eval(p: tuple, bounds: tuple[Q, Q]) -> tuple[Q, Q]:
    v = (Q(0), Q(0))
    for a in reversed(p):
        v = iadd(imul(v, bounds), interval(a))
    return v


class Root:
    """One real root, isolated by exact rational bounds (or an exact rational)."""
    def __init__(self, p: tuple, lo: Q, hi: Q, *, checked: bool = False):
        self.p = p
        self.lo, self.hi = Q(lo), Q(hi)
        self.chain = sturm(p)
        self._zero_cache: dict[tuple, bool] = {}
        self._sign_cache: dict[tuple, int] = {}
        if not checked:
            if lo == hi:
                if evaluate(p, lo) != 0:
                    raise ValueError('claimed rational root is not a root')
            elif root_count(self.chain, self.lo, self.hi) != 1:
                raise ValueError('interval does not isolate one root')

    def refine(self) -> None:
        if self.lo == self.hi:
            return
        m = (self.lo + self.hi) / 2
        if evaluate(self.p, m) == 0:
            self.lo = self.hi = m
        elif root_count(self.chain, self.lo, m) == 1:
            self.hi = m
        else:
            self.lo = m

    @staticmethod
    def cache_key(q: tuple) -> tuple:
        return tuple(('a', id(c.field), c.num, c.den) if isinstance(c, AElem)
                     else ('q', Q(c)) for c in q)

    def is_zero(self, q: tuple) -> bool:
        if not q:
            return True
        if self.lo == self.hi:
            return evaluate(q, self.lo) == 0
        key = self.cache_key(q)
        if key in self._zero_cache:
            return self._zero_cache[key]
        h = gcd(self.p, q)
        result = len(h) > 1 and root_count(sturm(h), self.lo, self.hi) == 1
        self._zero_cache[key] = result
        return result

    def sign_at(self, q: tuple) -> int:
        key = self.cache_key(q)
        if key in self._sign_cache:
            return self._sign_cache[key]
        if self.is_zero(q):
            self._sign_cache[key] = 0
            return 0
        # GCD decides equality; interval refinement is used only for nonzero values.
        for _ in range(MAX_REFINEMENTS):
            lo, hi = interval_eval(q, (self.lo, self.hi))
            if lo > 0 or hi < 0:
                s = 1 if lo > 0 else -1
                self._sign_cache[key] = s
                return s
            # Refine both the root and any algebraic coefficients.
            for a in q:
                if isinstance(a, AElem):
                    a.field.root.refine()
            self.refine()
        raise LimitExceeded('algebraic sign refinement limit')

    def descriptor(self) -> list[str]:
        return [str(self.lo), str(self.hi)]


class AField:
    """Q(alpha), represented without asserting irreducibility of root.p."""
    def __init__(self, root: Root):
        if not all(isinstance(c, Q) for c in root.p):
            raise TypeError('only rational base defining polynomials supported')
        self.root = root
        self.p = root.p

    def element(self, numerator: tuple = (), denominator: tuple = (Q(1),)) -> AElem:
        return AElem(self, numerator, denominator)

    def const(self, a: Any) -> AElem:
        return self.element((Q(a),))


class AElem:
    __slots__ = ('field', 'num', 'den')
    def __init__(self, field: AField, num: tuple, den: tuple = (Q(1),)):
        self.field = field
        num = divmod_poly(trim(Q(a) for a in num), field.p)[1]
        den = divmod_poly(trim(Q(a) for a in den), field.p)[1]
        if field.root.is_zero(den):
            raise ZeroDivisionError('algebraic denominator is zero at selected root')
        if field.root.is_zero(num):
            self.num, self.den = (), (Q(1),)
            return
        h = gcd(num, den)
        if len(h) > 1:
            num, den = quotient(num, h), quotient(den, h)
        c = 1 / den[-1]
        self.num, self.den = scale(num, c), scale(den, c)

    def coerce(self, b: Any) -> AElem:
        if isinstance(b, AElem):
            if b.field is not self.field:
                raise TypeError('different algebraic fields')
            return b
        return self.field.const(b)

    def __add__(self, b: Any) -> AElem:
        b = self.coerce(b)
        return AElem(self.field, add(mul(self.num, b.den), mul(b.num, self.den)),
                     mul(self.den, b.den))
    __radd__ = __add__

    def __neg__(self) -> AElem:
        return AElem(self.field, neg(self.num), self.den)

    def __sub__(self, b: Any) -> AElem:
        return self + (-self.coerce(b))

    def __rsub__(self, b: Any) -> AElem:
        return self.coerce(b) - self

    def __mul__(self, b: Any) -> AElem:
        b = self.coerce(b)
        return AElem(self.field, mul(self.num, b.num), mul(self.den, b.den))
    __rmul__ = __mul__

    def __truediv__(self, b: Any) -> AElem:
        b = self.coerce(b)
        return AElem(self.field, mul(self.num, b.den), mul(self.den, b.num))

    def __rtruediv__(self, b: Any) -> AElem:
        return self.coerce(b) / self

    def __eq__(self, b: Any) -> bool:
        if not isinstance(b, (int, Q, AElem)):
            return False
        b = self.coerce(b)
        return self.field.root.is_zero(sub(mul(self.num, b.den), mul(b.num, self.den)))

    __hash__ = None  # semantic equality; caches use explicit representation keys

    def sign(self) -> int:
        return self.field.root.sign_at(self.num) * self.field.root.sign_at(self.den)

    def interval(self) -> tuple[Q, Q]:
        for _ in range(MAX_REFINEMENTS):
            bounds = (self.field.root.lo, self.field.root.hi)
            n, d = interval_eval(self.num, bounds), interval_eval(self.den, bounds)
            if d[0] > 0 or d[1] < 0:
                return idiv(n, d)
            self.field.root.refine()
        raise LimitExceeded('algebraic coefficient enclosure limit')

    def __repr__(self) -> str:
        return f'AElem({self.num!r}/{self.den!r})'


def coefficient_at_x(poly: dict[tuple[int, int], Q], x: Q | AField) -> tuple:
    """Specialize a rational bivariate polynomial in x, retaining y."""
    if not poly:
        return ()
    max_y = max(j for _, j in poly)
    out = []
    for j in range(max_y + 1):
        terms = {i: c for (i, jj), c in poly.items() if jj == j}
        p = trim(terms.get(i, Q(0)) for i in range(max(terms, default=-1) + 1))
        out.append(x.element(p) if isinstance(x, AField) else Q(evaluate(p, x)))
    return trim(out)


def isolate_roots(p: tuple) -> list[Root]:
    """Complete exact bisection proposer, subject to explicit operation bounds."""
    p = squarefree(p)
    if len(p) <= 1:
        return []
    chain = sturm(p)
    n = total_roots(chain)
    if n == 0:
        return []
    max_coeff = Q(0)
    for a in p[:-1]:
        lo, hi = interval(a / p[-1])
        max_coeff = max(max_coeff, abs(lo), abs(hi))
    B = Q(max_coeff.numerator // max_coeff.denominator + 2)
    pending = [(-B, B, n)]
    roots: list[Root] = []
    nodes = 0
    while pending:
        nodes += 1
        if nodes > MAX_ISOLATION_NODES:
            raise LimitExceeded('root isolation node limit')
        lo, hi, n = pending.pop()
        if n == 0:
            continue
        if n == 1:
            r = Root(p, lo, hi, checked=True)
            # Extra refinement separates cuts and recognizes simple rational samples.
            for _ in range(3):
                r.refine()
            roots.append(r)
            continue
        m = (lo + hi) / 2
        k = 3
        while evaluate(p, m) == 0:
            # Choose a nonroot split. A degree-d polynomial has at most d roots.
            m = lo + (hi - lo) / k
            k += 1
            if k > len(p) + 5:
                raise ArithmeticError('failed to choose nonroot split')
        nl = root_count(chain, lo, m)
        pending.append((m, hi, n - nl))
        pending.append((lo, m, nl))
    roots.sort(key=lambda r: r.lo)
    for a, b in zip(roots, roots[1:]):
        for _ in range(MAX_REFINEMENTS):
            if a.hi < b.lo:
                break
            a.refine(); b.refine()
        else:
            raise LimitExceeded('separating adjacent root cuts')
    return roots


def verify_root_cover(p: tuple, descriptors: list) -> list[Root]:
    """Check intervals, disjointness and equality to the total Sturm root count."""
    p = squarefree(p)
    roots = [Root(p, parse_q(pair[0]), parse_q(pair[1])) for pair in descriptors
             if isinstance(pair, list) and len(pair) == 2]
    if len(roots) != len(descriptors):
        raise ValueError('malformed root descriptor')
    if len(roots) != total_roots(sturm(p)):
        raise ValueError('incomplete/excess root coverage')
    if any(a.hi >= b.lo for a, b in zip(roots, roots[1:])):
        raise ValueError('root cuts overlap or are out of order')
    return roots


def sector_samples(roots: list[Root]) -> list[Q]:
    if not roots:
        return [Q(0)]
    return ([roots[0].lo - 1]
            + [(a.hi + b.lo) / 2 for a, b in zip(roots, roots[1:])]
            + [roots[-1].hi + 1])


def sample_in_sector(q: Q, roots: list[Root], index: int) -> bool:
    # Exact comparisons to root values, not merely to their current enclosures.
    if index > 0 and roots[index - 1].sign_at((-q, Q(1))) >= 0:
        return False
    if index < len(roots) and roots[index].sign_at((-q, Q(1))) <= 0:
        return False
    return True


def parse_q(value: Any) -> Q:
    """Canonical exact strings only. In particular JSON floats are not rationals."""
    if not isinstance(value, str) or len(value) > 20000:
        raise ValueError('rational must be a bounded canonical string')
    q = Q(value)
    if str(q) != value:
        raise ValueError('noncanonical rational')
    return q
