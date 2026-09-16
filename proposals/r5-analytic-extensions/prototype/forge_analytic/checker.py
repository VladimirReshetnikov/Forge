"""Standalone exact replay. Imports no search module or external numerical package.

This uses sparse polynomials, whereas search uses dense polynomials. Both
implement the same *mathematical* rules; neither implementation is verified.
The source subject is always supplied externally, not taken on the certificate's
word. JSON decoding rejects duplicate keys and noncanonical rational strings.
"""
from __future__ import annotations
import json
import re
from fractions import Fraction as F
from math import comb, factorial

Rat = F
SP = dict[int, F]
IV = tuple[F, F]

class Rejected(ValueError):
    pass

def require(test: bool, reason: str) -> None:
    if not test:
        raise Rejected(reason)

def integer(n: object, lo: int, hi: int) -> int:
    require(type(n) is int and lo <= n <= hi, 'integer out of bounds')
    return n  # type: ignore[return-value]

def rat(s: object) -> F:
    require(type(s) is str and len(s) <= 400, 'rational string required')
    require(bool(re.fullmatch(r'-?(0|[1-9][0-9]*)/[1-9][0-9]*', s)), 'rational syntax')
    q = F(s)
    require(f'{q.numerator}/{q.denominator}' == s, 'noncanonical rational')
    require(max(q.numerator.bit_length(), q.denominator.bit_length()) <= 1024, 'rational too large')
    return q

def sp(xs: object) -> SP:
    require(type(xs) is list and 1 <= len(xs) <= 193, 'polynomial length')
    vals = [rat(x) for x in xs]
    require(len(vals) == 1 or vals[-1] != 0, 'polynomial not trimmed')
    return {i: v for i, v in enumerate(vals) if v}

def sm(a: SP, b: SP) -> SP:
    out: SP = {}
    for i, c in a.items():
        for j, d in b.items():
            out[i+j] = out.get(i+j, F(0)) + c*d
    return {i: c for i, c in out.items() if c}

def sa(a: SP, b: SP, multiplier: F = F(1)) -> SP:
    out = dict(a)
    for i, v in b.items():
        out[i] = out.get(i, F(0))+multiplier*v
    return {i: c for i, c in out.items() if c}

def sc(a: SP, c: F) -> SP:
    return {i: c*v for i, v in a.items() if c*v}

def powsp(a: SP, p: int) -> SP:
    r = {0: F(1)}
    for _ in range(p):
        r = sm(r, a)
    return r

def shiftsp(a: SP, n: int) -> SP:
    r: SP = {}
    for j, c in a.items():
        for k in range(j+1):
            r[k] = r.get(k, F(0)) + c*comb(j, k)*F(n)**(j-k)
    return {i: c for i, c in r.items() if c}

def interval(xs: object) -> IV:
    require(type(xs) is list and len(xs) == 2, 'interval shape')
    lo, hi = rat(xs[0]), rat(xs[1])
    require(lo <= hi, 'reversed interval')
    return lo, hi

def iadd(a: IV, b: IV) -> IV:
    return a[0]+b[0], a[1]+b[1]

def iprod(a: IV, b: IV) -> IV:
    products = (a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1])
    return min(products), max(products)

def polybox(p: SP, b: F) -> IV:
    # Sparse representation, Horner evaluation with all missing degrees made explicit.
    out: IV = (F(0), F(0))
    for i in range(max(p, default=0), -1, -1):
        c = p.get(i, F(0))
        out = iadd(iprod((F(0), b), out), (c, c))
    return out

def bounds(expr: object, b: F, k: int, depth: int = 0, count: list[int] | None = None) -> tuple[SP, IV]:
    if count is None:
        count = [0]
    count[0] += 1
    require(depth <= 32 and count[0] <= 256, 'expression budget')
    require(type(expr) is list and len(expr) >= 1 and type(expr[0]) is str, 'AST node')
    op = expr[0]
    if op == 'poly':
        require(len(expr) == 2, 'polynomial node arity')
        p = sp(expr[1])
        low = {i: c for i, c in p.items() if i < k}
        high = {i-k: c for i, c in p.items() if i >= k}
        return low, polybox(high, b)
    if op == 'neg':
        require(len(expr) == 2, 'negation arity')
        p, I = bounds(expr[1], b, k, depth+1, count)
        return sc(p, F(-1)), (-I[1], -I[0])
    if op in ('add', 'mul'):
        require(len(expr) == 3, 'binary node arity')
        p, I = bounds(expr[1], b, k, depth+1, count)
        q, J = bounds(expr[2], b, k, depth+1, count)
        if op == 'add':
            return sa(p, q), iadd(I, J)
        pq = sm(p, q)
        low = {i: c for i, c in pq.items() if i < k}
        high = {i-k: c for i, c in pq.items() if i >= k}
        E = polybox(high, b)
        E = iadd(E, iprod(polybox(p, b), J))
        E = iadd(E, iprod(polybox(q, b), I))
        E = iadd(E, iprod((F(0), b**k), iprod(I, J)))
        return low, E
    require(op in ('exp', 'sin', 'cos', 'log1p', 'atan') and len(expr) == 2, 'unsupported atom')
    a = rat(expr[1])
    p: SP = {}
    for i in range(k):
        c = F(0)
        if op == 'exp':
            c = a**i/F(factorial(i))
        elif op == 'sin' and i % 2 == 1:
            c = (-1)**((i-1)//2)*a**i/F(factorial(i))
        elif op == 'cos' and i % 2 == 0:
            c = (-1)**(i//2)*a**i/F(factorial(i))
        elif op == 'log1p' and i > 0:
            c = (-1)**(i+1)*a**i/F(i)
        elif op == 'atan' and i % 2 == 1:
            c = (-1)**((i-1)//2)*a**i/F(i)
        if c:
            p[i] = c
    if op in ('exp', 'sin', 'cos'):
        rho = abs(a)*b/F(k+1)
        require(rho < 1, 'majorant ratio')
        R = abs(a)**k/(F(factorial(k))*(1-rho))
    else:
        require(abs(a)*b < 1, 'analytic domain')
        R = abs(a)**k/(F(k)*(1-abs(a)*b))
    return p, (-R, R)

def fields(obj: object, keys: set[str]) -> dict:
    require(type(obj) is dict and set(obj) == keys, 'object fields')
    return obj  # type: ignore[return-value]

def check_anchored(s: dict, c: dict) -> None:
    fields(s, {'expr', 'b'})
    fields(c, {'kind', 'subject', 'order', 'polynomial', 'error', 'valuation', 'margin'})
    b, k = rat(s['b']), integer(c['order'], 1, 40)
    require(0 < b <= 16, 'box bound')
    p, I = bounds(s['expr'], b, k)
    require(sp(c['polynomial']) == p and interval(c['error']) == I, 'jet mismatch')
    m = integer(c['valuation'], 0, k)
    require(m == min(p, default=k), 'incorrect vanishing order')
    if m == k:
        lower = I[0]
    else:
        quotient = {i-m: v for i, v in p.items()}
        lower = iadd(polybox(quotient, b), iprod((F(0), b**(k-m)), I))[0]
    require(rat(c['margin']) == lower and lower >= 0, 'nonnegative margin missing')

def exppoly(xs: object) -> dict[F, SP]:
    require(type(xs) is list and len(xs) <= 32, 'exponential polynomial size')
    out: dict[F, SP] = {}
    previous: F | None = None
    for row in xs:
        require(type(row) is list and len(row) == 2, 'exponential row')
        a, p = rat(row[0]), sp(row[1])
        require(p != {} and a not in out and (previous is None or previous < a), 'exponential canonical form')
        out[a], previous = p, a
    return out

def nextstage(f: dict[F, SP], rate: F) -> dict[F, SP]:
    g: dict[F, SP] = {}
    for a, p in f.items():
        q = sc(p, a-rate)
        for j, value in p.items():
            if j:
                q[j-1] = q.get(j-1, F(0))+j*value
        q = {i: v for i, v in q.items() if v}
        if q:
            g[a] = q
    return g

def check_ladder(s: dict, c: dict) -> None:
    fields(s, {'exp_poly', 'domain'})
    fields(c, {'kind', 'subject', 'rates', 'stages', 'seeds', 'search_nodes'})
    require(s['domain'] == 'x>=0', 'unsupported global domain')
    require(type(c['rates']) is list and len(c['rates']) <= 32, 'ladder depth')
    rates = [rat(x) for x in c['rates']]
    require(type(c['stages']) is list and len(c['stages']) == len(rates)+1, 'stage count')
    require(type(c['seeds']) is list and len(c['seeds']) == len(rates)+1, 'seed count')
    integer(c['search_nodes'], 1, 10**7)  # Metadata only, never evidence of validity.
    current = exppoly(s['exp_poly'])
    for i in range(len(rates)+1):
        require(exppoly(c['stages'][i]) == current, 'differential identity failed')
        atzero = sum((p.get(0, F(0)) for p in current.values()), F(0))
        require(rat(c['seeds'][i]) == atzero and atzero >= 0, 'negative/mismatched boundary seed')
        if i < len(rates):
            current = nextstage(current, rates[i])
    require(all(v >= 0 for p in current.values() for v in p.values()), 'terminal cone failed')

def tail_subject(s: dict) -> tuple[SP, SP]:
    fields(s, {'numerator', 'denominator', 'interpretation'})
    require(s['interpretation'] == 'eventual-rational-tail', 'tail semantics')
    A, D = sp(s['numerator']), sp(s['denominator'])
    require(bool(D), 'zero denominator polynomial')
    return A, D

def nonnegative(p: SP) -> bool:
    return all(v >= 0 for v in p.values())

def check_barrier(s: dict, c: dict) -> None:
    fields(c, {'kind', 'subject', 'cutoff', 'shift', 'power', 'constant',
               'shifted_numerator', 'shifted_denominator', 'shifted_residual', 'tail_bound'})
    A, D = tail_subject(s)
    N, shift, p = integer(c['cutoff'], 1, 10**6), integer(c['shift'], -4096, 4096), integer(c['power'], 1, 16)
    C = rat(c['constant'])
    require(C > 0 and N+shift >= 1, 'barrier domain')
    u = powsp({0: F(shift), 1: F(1)}, p)
    v = powsp({0: F(shift+1), 1: F(1)}, p)
    residual = sa(sc(sm(sa(v, u, F(-1)), D), C), sm(A, sm(u, v)), F(-1))
    ash, dsh, rsh = shiftsp(A, N), shiftsp(D, N), shiftsp(residual, N)
    require(sp(c['shifted_numerator']) == ash and nonnegative(ash), 'numerator certificate')
    require(sp(c['shifted_denominator']) == dsh and nonnegative(dsh) and dsh.get(0, F(0)) > 0, 'denominator positivity')
    require(sp(c['shifted_residual']) == rsh and nonnegative(rsh), 'barrier residual')
    require(rat(c['tail_bound']) == C/F(N+shift)**p, 'tail bound mismatch')

def check_divergence(s: dict, c: dict) -> None:
    fields(c, {'kind', 'subject', 'cutoff', 'minorant', 'shifted_denominator', 'shifted_residual'})
    A, D = tail_subject(s)
    N, low = integer(c['cutoff'], 1, 10**6), rat(c['minorant'])
    require(low > 0, 'minorant must be strictly positive')
    residual = sa(sm({1: F(1)}, A), sc(D, low), F(-1))
    ds, rs = shiftsp(D, N), shiftsp(residual, N)
    require(sp(c['shifted_denominator']) == ds and nonnegative(ds) and ds.get(0, F(0)) > 0, 'denominator positivity')
    require(sp(c['shifted_residual']) == rs and nonnegative(rs), 'harmonic minorant residual')

def verify(subject: dict, certificate: dict) -> bool:
    """Check a candidate against an externally supplied exact subject.

    Acceptance is Python evidence for the named certificate theorem. It is not
    a theorem of Lean and does not verify the source-to-subject translation.
    """
    try:
        require(type(certificate) is dict and type(subject) is dict, 'envelope type')
        require(certificate.get('subject') == subject, 'wrong subject')
        kind = certificate.get('kind')
        if kind == 'anchored':
            check_anchored(subject, certificate)
        elif kind == 'ladder':
            check_ladder(subject, certificate)
        elif kind == 'barrier':
            check_barrier(subject, certificate)
        elif kind == 'divergence':
            check_divergence(subject, certificate)
        else:
            raise Rejected('unknown certificate kind')
        return True
    except (Rejected, ValueError, TypeError, KeyError, IndexError, ZeroDivisionError, OverflowError, RecursionError):
        return False

def loads(data: str) -> dict:
    require(type(data) is str and len(data.encode('utf-8')) <= 2_000_000, 'JSON byte limit')
    def pairs(xs: list[tuple[str, object]]) -> dict:
        out: dict = {}
        for k, v in xs:
            require(k not in out, 'duplicate JSON key')
            out[k] = v
        return out
    def reject_float(_: str) -> None:
        raise Rejected('floating-point JSON is prohibited')
    result = json.loads(data, object_pairs_hook=pairs, parse_float=reject_float, parse_constant=reject_float)
    require(type(result) is dict, 'JSON envelope must be an object')
    return result
