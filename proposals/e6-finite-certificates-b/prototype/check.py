"""Independent exact certificate replay. Standard library only.

The search modules do not import this module. Acceptance here establishes the
finite algebraic obligations in the accompanying mathematical soundness proofs;
it is not a Lean-kernel receipt. Inputs are bounded, versioned data, never code.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb, factorial
import json
from pathlib import Path
from typing import Any

MAX_TERMS = 30000
MAX_DIM = 64
MAX_EXP = 100
MAX_BITS = 16384
MAX_BYTES = 16000000
Poly = dict[tuple[int, ...], Q]

class Rejected(ValueError):
    pass

def require(ok: bool, msg: str) -> None:
    if not ok:
        raise Rejected(msg)

def integer(x: Any, lo: int | None = None, hi: int | None = None) -> int:
    require(type(x) is int, 'integer required; booleans and floats forbidden')
    require(x.bit_length() <= MAX_BITS, 'oversized integer')
    require(lo is None or x >= lo, 'integer below bound')
    require(hi is None or x <= hi, 'integer above bound')
    return x

def rat(x: Any) -> Q:
    require(type(x) is list and len(x) == 2, 'rational pair required')
    a, b = integer(x[0]), integer(x[1], 1)
    z = Q(a, b)
    require((z.numerator, z.denominator) == (a, b), 'noncanonical rational')
    return z

def poly(x: Any, n: int) -> Poly:
    require(type(x) is list and len(x) <= MAX_TERMS, 'bad polynomial')
    out: Poly = {}
    prev = None
    for term in x:
        require(type(term) is list and len(term) == 2, 'bad term')
        exp, c = term
        require(type(exp) is list and len(exp) == n, 'exponent dimension')
        e = tuple(integer(v, 0, MAX_EXP) for v in exp)
        c = rat(c)
        require(c != 0 and (prev is None or prev < e), 'zero, duplicate or unsorted term')
        out[e] = c
        prev = e
    return out

def const(c: int | Q, n: int) -> Poly:
    return {} if c == 0 else {(0,) * n: Q(c)}

def var(i: int, n: int) -> Poly:
    return {tuple(int(j == i) for j in range(n)): Q(1)}

def add(a: Poly, b: Poly) -> Poly:
    c = dict(a)
    for e, v in b.items():
        c[e] = c.get(e, Q(0)) + v
        if c[e] == 0:
            del c[e]
    require(len(c) <= MAX_TERMS, 'polynomial work budget')
    return c

def scale(a: Poly, q: Q | int) -> Poly:
    return {e: v*q for e, v in a.items() if v*q}

def mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for ea, va in a.items():
        for eb, vb in b.items():
            e = tuple(x+y for x, y in zip(ea, eb, strict=True))
            out[e] = out.get(e, Q(0)) + va*vb
    out = {e: v for e, v in out.items() if v}
    require(len(out) <= MAX_TERMS, 'polynomial work budget')
    return out

def power(a: Poly, k: int, n: int) -> Poly:
    z = const(1, n)
    while k:
        if k & 1:
            z = mul(z, a)
        a = mul(a, a)
        k //= 2
    return z

def compose(a: Poly, images: list[Poly], codim: int) -> Poly:
    out: Poly = {}
    for e, c in a.items():
        require(len(e) == len(images), 'substitution dimension')
        t = const(c, codim)
        for im, k in zip(images, e, strict=True):
            t = mul(t, power(im, k, codim))
        out = add(out, t)
    return out

def lincomb(coeff: list[Poly], terms: list[Poly]) -> Poly:
    require(len(coeff) == len(terms), 'multiplier count')
    z: Poly = {}
    for c, t in zip(coeff, terms, strict=True):
        z = add(z, mul(c, t))
    return z

def verify_ideal(problem: dict, cert: dict) -> dict:
    n = integer(problem['dimension'], 1, MAX_DIM)
    require(cert['kind'] == 'inductive_ideal_v1', 'wrong certificate kind')
    inv = [poly(p, n) for p in cert['invariants']]
    require(len(inv) <= 512, 'too many invariants')
    goal = poly(problem['goal'], n)
    require(problem['initial'], 'initial descriptions missing')
    require(problem['transitions'], 'transition descriptions missing')
    for initial in problem['initial']:
        q = integer(initial['parameters'], 0, MAX_DIM)
        ims = [poly(p, q) for p in initial['values']]
        require(len(ims) == n, 'initial dimension')
        for p in inv:
            require(compose(p, ims, q) == {}, 'initial invariant fails')
    require(len(cert['steps']) == len(problem['transitions']), 'missing transition')
    for tr, steps in zip(problem['transitions'], cert['steps'], strict=True):
        ims = [poly(p, n) for p in tr['update']]
        gs = [poly(p, n) for p in tr['guards']]
        require(len(ims) == n and len(steps) == len(inv), 'step dimension')
        for p, cs in zip(inv, steps, strict=True):
            coeff = [poly(t, n) for t in cs]
            require(compose(p, ims, n) == lincomb(coeff, inv+gs), 'transition identity fails')
    coeff = [poly(t, n) for t in cert['goal_multipliers']]
    require(goal == lincomb(coeff, inv), 'goal ideal identity fails')
    return {'invariants': len(inv), 'transitions': len(problem['transitions'])}

def vector(v: Any, n: int) -> list[Q]:
    require(type(v) is list and len(v) == n, 'vector dimension')
    return [rat(c) for c in v]

def matrix(v: Any, r: int, c: int) -> list[list[Q]]:
    require(type(v) is list and len(v) == r, 'matrix row dimension')
    return [vector(row, c) for row in v]

def rowmul(v: list[Q], m: list[list[Q]], cols: int) -> list[Q]:
    require(len(v) == len(m), 'matrix product dimension')
    return [sum((v[i]*m[i][j] for i in range(len(v))), Q(0)) for j in range(cols)]

def matmul(a: list[list[Q]], b: list[list[Q]], cols: int) -> list[list[Q]]:
    return [rowmul(row, b, cols) for row in a]

def verify_weighted(problem: dict, cert: dict) -> dict:
    n = integer(problem['dimension'], 1, MAX_DIM)
    alpha, beta = vector(problem['alpha'], n), vector(problem['beta'], n)
    labels = problem['alphabet']
    require(type(labels) is list and len(labels) <= MAX_DIM, 'bad alphabet')
    require(all(type(a) is str for a in labels) and len(set(labels)) == len(labels), 'duplicate label')
    require(set(problem['matrices']) == set(labels), 'source transition inventory')
    ms = {a: matrix(problem['matrices'][a], n, n) for a in labels}
    if cert['kind'] == 'distinguishing_word_v1':
        word = cert['word']
        require(type(word) is list and len(word) <= 100000, 'bad word')
        v = alpha
        for a in word:
            require(a in ms, 'unknown letter')
            v = rowmul(v, ms[a], n)
        value = sum((a*b for a, b in zip(v, beta, strict=True)), Q(0))
        require(value != 0, 'word does not distinguish')
        return {'word_length': len(word), 'value': [value.numerator, value.denominator]}
    require(cert['kind'] == 'weighted_closure_v1', 'wrong certificate kind')
    r = integer(cert['rank'], 0, MAX_DIM)
    b = matrix(cert['basis'], r, n)
    c0 = vector(cert['initial_coordinates'], r)
    require(alpha == rowmul(c0, b, n), 'initial span fails')
    require(set(cert['closure']) == set(labels), 'missing closure letter')
    for a in labels:
        c = matrix(cert['closure'][a], r, r)
        require(matmul(b, ms[a], n) == matmul(c, b, n), 'closure identity fails')
    require(all(sum((x*y for x,y in zip(row,beta,strict=True)), Q(0)) == 0 for row in b), 'output does not vanish')
    return {'basis_rows': r, 'dimension': n, 'letters': len(labels)}

def rising_n(start: int, stop: int, n: Poly) -> Poly:
    # product_{j=start}^{stop} (n+j), in the one-variable polynomial ring.
    out = const(1, 1)
    for j in range(start, stop+1):
        out = mul(out, add(n, const(j, 1)))
    return out

def binomial_n_plus_choose(n: Poly, offset: int, k: int) -> Poly:
    if k < 0:
        return {}
    out = const(Q(1, factorial(k)), 1)
    for j in range(k):
        out = mul(out, add(n, const(offset-j, 1)))
    return out

def verify_telescoper(problem: dict, cert: dict) -> dict:
    require(problem['family'] == 'binomial_power_sum', 'unsupported summand family')
    m = integer(problem['power'], 1, 8)
    require(cert['kind'] == 'binomial_telescoper_v1', 'wrong certificate kind')
    r = integer(cert['order'], 1, 5)
    p = [poly(t, 1) for t in cert['coefficients']]
    require(len(p) == r+1, 'recurrence coefficient count')
    u = poly(cert['numerator'], 2)
    n, k = var(0, 2), var(1, 2)
    n1 = var(0, 1)
    pp = [compose(t, [n], 2) for t in p]
    left: Poly = {}
    for j in range(r+1):
        z = pp[j]
        for t in range(1, j+1):
            z = mul(z, power(add(n, const(t, 2)), m, 2))
        for t in range(j+1, r+1):
            z = mul(z, power(add(add(n, const(t, 2)), scale(k, -1)), m, 2))
        left = add(left, z)
    uk1 = compose(u, [n, add(k, const(1, 2))], 2)
    right = add(mul(power(add(add(n, const(r, 2)), scale(k, -1)), m, 2), uk1),
                scale(mul(power(k, m, 2), u), -1))
    require(left == right, 'interior polynomial identity fails')
    # Regularized certificate: H(n,k)=U(n,k)*binom(n+r-1,k-1)^m.
    # Its scalar multiplier on the recurrence is A(n)^m, A=(n+1)...(n+r-1).
    a = power(rising_n(1, r-1, n1), m, 1)
    # k=0 is outside the ratio argument: check it symbolically, not by cancellation.
    lhs0 = mul(a, lincomb([const(1,1)]*(r+1), p))
    rhs0 = compose(u, [n1, const(1,1)], 1)
    require(lhs0 == rhs0, 'lower boundary identity fails')
    # Remaining ratio poles k=n+t, t=1..r are checked as polynomial identities.
    for t in range(1, r+1):
        ls: Poly = {}
        for j in range(t, r+1):
            bj = binomial_n_plus_choose(n1, j, j-t)
            ls = add(ls, mul(p[j], power(bj, m, 1)))
        ls = mul(a, ls)
        def h_at(s: int) -> Poly:
            b = binomial_n_plus_choose(n1, r-1, r-s)
            uv = compose(u, [n1, add(n1, const(s,1))], 1)
            return mul(uv, power(b,m,1))
        require(ls == add(h_at(t+1), scale(h_at(t),-1)), 'upper boundary identity fails')
    # p_r(n)>0 or <0 for n>=0: this small checker accepts coefficient-positive p_r or -p_r.
    lead = p[-1]
    require(bool(lead), 'zero leading recurrence coefficient')
    sign = 1 if lead.get((0,), Q(0)) > 0 else -1
    require(sign*lead.get((0,),Q(0)) > 0 and all(sign*c >= 0 for c in lead.values()), 'leading coefficient positivity not established')
    initials = [sum(comb(i,j)**m for j in range(i+1)) for i in range(r)]
    require(cert['initial_values'] == initials and all(type(v) is int for v in cert['initial_values']), 'initial values incorrect')
    return {'power':m, 'order':r, 'initial_values': initials, 'boundary_rows':r+1}

def verify(problem: dict, cert: dict) -> dict:
    kind = problem.get('kind')
    if kind == 'inductive_ideal_problem_v1':
        return verify_ideal(problem, cert)
    if kind == 'weighted_problem_v1':
        return verify_weighted(problem, cert)
    if kind == 'telescoping_problem_v1':
        return verify_telescoper(problem, cert)
    raise Rejected('unsupported problem kind')

def no_duplicates(pairs: list) -> dict:
    d = {}
    for k, v in pairs:
        require(k not in d, 'duplicate JSON key')
        d[k] = v
    return d

def load(path: str | Path) -> Any:
    raw = Path(path).read_bytes()
    require(len(raw) <= MAX_BYTES, 'file too large')
    return json.loads(raw, object_pairs_hook=no_duplicates,
                      parse_float=lambda _: (_ for _ in ()).throw(Rejected('float token')),
                      parse_constant=lambda _: (_ for _ in ()).throw(Rejected('nonfinite token')))
