"""Receipt replay. No import of the search module. No float acceptance.

The ladder verifier uses a coefficient stencil distinct from the producer's
term-wise differentiator. Tail inequalities are checked from their sufficient
conditions, not by re-running the proposer. Interval replay deliberately shares
bounds.py with search; tests disclose and address (not eliminate) that risk.
"""
from fractions import Fraction as Q
from math import factorial
from .core import decode, encode, rat, origin
from .bounds import exp_bounds, point_bounds


def checked_op(a, rho):
    out = {}
    rates = sorted(set(r for r, _ in a))
    for r in rates:
        max_degree = max(k for s, k in a if s == r)
        for k in range(max_degree+1):
            c = (r-rho)*a.get((r, k), Q(0))+(k+1)*a.get((r, k+1), Q(0))
            if c:
                out[(r, k)] = c
    return out


def interval_mul(a, b):
    vals = [x*y for x in a for y in b]
    return min(vals), max(vals)


def interval_value(a, left, right, bits=96, order=32):
    # Normalize by one positive exp(constant) over the WHOLE leaf. Normalizing
    # each term separately would be unsound. Bounds avoid positive exp calls.
    shift = max([Q(0)]+[max(r*left, r*right) for r, _ in a])
    out = (Q(0), Q(0))
    rates = sorted(set(r for r, _ in a))
    for r in rates:
        degree = max(k for s, k in a if s == r)
        p = (Q(0), Q(0))
        for k in range(degree, -1, -1):
            p = interval_mul(p, (left, right))
            c = a.get((r, k), Q(0))
            p = (p[0]+c, p[1]+c)
        ea, eb = sorted((r*left-shift, r*right-shift))
        elo, _ = exp_bounds(ea, bits, order)
        _, ehi = exp_bounds(eb, bits, order)
        t = interval_mul(p, (elo, ehi))
        out = (out[0]+t[0], out[1]+t[1])
    return out


def _budget(cert):
    bits, order = cert.get('bits'), cert.get('order')
    if type(bits) is not int or not 8 <= bits <= 4096:
        raise ValueError('invalid precision')
    if type(order) is not int or not 1 <= order <= 4096:
        raise ValueError('invalid order')
    return bits, order


def _ladder(a, cert):
    anchor = rat(cert['anchor'])
    bits, order = _budget(cert)
    steps = cert['steps']
    if not isinstance(steps, list) or len(steps) > 4096:
        return False
    current = a
    for step in steps:
        claimed = decode(step['polynomial'])
        if claimed != current:
            return False
        lo, hi = point_bounds(current, anchor, bits, order)
        if lo != rat(step['lower']) or hi != rat(step['upper']) or lo < 0:
            return False
        current = checked_op(current, rat(step['rho']))
    return not current


def _tail(a, cert):
    sign, X = cert['sign'], rat(cert['cutoff'])
    if type(sign) is not int or sign not in (-1, 0, 1) or X < 1:
        return False
    if not a:
        return sign == 0 and cert['orders'] == []
    if sign == 0:
        return False
    leading_rate = max(r for r, _ in a)
    leading_degree = max(k for r, k in a if r == leading_rate)
    leading = sign*a[(leading_rate, leading_degree)]
    if leading <= 0:
        return False
    lower = sum((abs(c) for (r, k), c in a.items()
                         if r == leading_rate and k < leading_degree), Q(0))
    if leading*X < 2*lower:
        return False
    others = sorted(set(r for r, _ in a if r != leading_rate))
    orders = cert['orders']
    if not isinstance(orders, list) or len(orders) != len(others):
        return False
    B = Q(0)
    for row, rate in zip(orders, others):
        if not isinstance(row, list) or len(row) != 2 or rat(row[0]) != rate:
            return False
        k = row[1]
        degree = max(j for r, j in a if r == rate)
        if type(k) is not int or not 1 <= k <= 4096:
            return False
        if k < degree-leading_degree+1:
            return False
        C = sum((abs(c) for (r, _), c in a.items() if r == rate), Q(0))
        B += C*Q(factorial(k))/(leading_rate-rate)**k
    return leading*X >= 4*B


def _cover(a, cert):
    bits, order = _budget(cert)
    l, r = map(rat, cert['domain'])
    if l > r:
        return False
    visited = [0]
    def walk(node, left, right, depth):
        visited[0] += 1
        if depth > 128 or visited[0] > 500000:
            return False
        if 'leaf' in node:
            if node['leaf'] != [str(left), str(right)]:
                return False
            lo, hi = interval_value(a, left, right, bits, order)
            return lo >= 0 and rat(node['lower']) == lo and rat(node['upper']) == hi
        mid = rat(node['split'])
        return (left < mid < right and walk(node['left'], left, mid, depth+1)
                and walk(node['right'], mid, right, depth+1))
    return walk(cert['tree'], l, r, 0)


def _counterpoint(a, cert):
    bits, order = _budget(cert)
    l, r = map(rat, cert['domain'])
    x = rat(cert['counterpoint'])
    if not l <= x <= r:
        return False
    lo, hi = point_bounds(a, x, bits, order)
    return hi < 0 and rat(cert['lower']) == lo and rat(cert['upper']) == hi


def verify(a, cert):
    """Check a receipt against an INDEPENDENTLY supplied original problem."""
    try:
        kind = cert['kind']
        funcs = {'ladder-v1': _ladder, 'tail-v1': _tail,
                 'cover-v1': _cover, 'counterpoint-v1': _counterpoint}
        return bool(funcs[kind](a, cert))
    except (ValueError, KeyError, TypeError, IndexError, ZeroDivisionError,
            OverflowError, RecursionError):
        return False


def verify_goal(problem, cert):
    """Bind receipt conclusion to the requested goal; never silently shrink it.

A certified tail is not a certificate on the original ray. A negative point
is a refutation, not a successful proof of a nonnegativity request.
"""
    try:
        a = decode(problem['polynomial'])
        if not verify(a, cert):
            return False
        goal = problem['goal']
        kind = goal['kind']
        if kind in ('nonnegative_ray', 'positive_open_ray', 'positive_closed_ray'):
            if cert['kind'] != 'ladder-v1' or rat(goal['anchor']) != rat(cert['anchor']):
                return False
            if kind == 'positive_open_ray':
                return any(rat(s['lower']) > 0 for s in cert['steps'])
            if kind == 'positive_closed_ray':
                return bool(cert['steps']) and rat(cert['steps'][0]['lower']) > 0
            return True
        if kind == 'eventual_sign':
            return cert['kind'] == 'tail-v1' and type(goal['sign']) is int and goal['sign'] == cert['sign']
        if kind == 'nonnegative_interval':
            return cert['kind'] == 'cover-v1' and goal['domain'] == cert['domain']
        if kind == 'counterexample_interval':
            return cert['kind'] == 'counterpoint-v1' and goal['domain'] == cert['domain']
        return False
    except (ValueError, KeyError, TypeError, IndexError, ZeroDivisionError):
        return False
