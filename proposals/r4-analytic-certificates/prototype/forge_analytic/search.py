"""Untrusted proposers: canonical ladders, auxiliary factors, tails and covers."""
from fractions import Fraction as Q
from math import factorial
from .core import op, spectrum, origin, encode, reflect, rat, scale
from .bounds import point_bounds


def ladder(a, anchor=0, factors=None, bits=96, order=32):
    anchor = rat(anchor)
    factors = spectrum(a) if factors is None else list(map(rat, factors))
    current, steps = a, []
    for rho in factors:
        lo, hi = point_bounds(current, anchor, bits, order)
        if lo < 0:
            return None
        steps.append({'rho': str(rho), 'polynomial': encode(current),
                      'lower': str(lo), 'upper': str(hi)})
        current = op(current, rho)
    if current:
        return None
    return {'kind': 'ladder-v1', 'anchor': str(anchor), 'bits': bits,
            'order': order, 'steps': steps}


def ghost_search(a, shifts=None, max_extra=96):
    """Add repeated factors below the native spectrum. Bounded, not complete."""
    direct = ladder(a)
    if direct is not None:
        return direct
    native = spectrum(a)
    if not native:
        return ladder(a)
    shifts = shifts or [min(native)-Q(b) for b in [1, 2, 4, 8, 16, 32, 64]]
    for beta in shifts:
        current = a
        prefix = []
        for _ in range(max_extra):
            if origin(current) < 0:
                break
            prefix.append(beta)
            current = op(current, beta)
            # A failed native suffix does not prevent adding another ghost.
            if ladder(current) is not None:
                return ladder(a, factors=prefix+native)
    return None


def tail(a):
    """Total on canonical nonzero inputs, apart from host resource exhaustion.

Return an explicit eventual sign and a rational X >= 1. A checker derives the
bound independently. This is not a positivity claim on [0,X).
"""
    if not a:
        return {'kind': 'tail-v1', 'sign': 0, 'cutoff': '1', 'orders': []}
    leading_rate = max(r for r, _ in a)
    d = max(k for r, k in a if r == leading_rate)
    lc = a[(leading_rate, d)]
    sign = 1 if lc > 0 else -1
    lc = abs(lc)
    lower = sum((abs(c) for (r, k), c in a.items()
                         if r == leading_rate and k < d), Q(0))
    rates = sorted(set(r for r, _ in a if r != leading_rate))
    B, orders = Q(0), []
    for r in rates:
        degree = max(k for s, k in a if s == r)
        C = sum((abs(c) for (s, _), c in a.items() if s == r), Q(0))
        k = max(degree-d, 0)+1
        B += C*factorial(k)/(leading_rate-r)**k
        orders.append([str(r), k])
    X = max(Q(1), 2*lower/lc, 4*B/lc)
    return {'kind': 'tail-v1', 'sign': sign, 'cutoff': str(X),
            'orders': orders}


def compact_cover(a, left, right, max_depth=16, bits=96, order=32):
    """Prove a>=0 on a closed interval, or return an exact rational counterpoint.

At each leaf use natural polynomial intervals and the monotonicity of exp.
This simple cover is a reference integration demonstrator, not a replacement
for existing Lean interval packages or Forge's polynomial Bernstein worker.
"""
    from .check import interval_value
    left, right = rat(left), rat(right)
    if left > right:
        raise ValueError('reversed interval')
    def visit(l, r, depth):
        lo, hi = interval_value(a, l, r, bits, order)
        if lo >= 0:
            return {'leaf': [str(l), str(r)], 'lower': str(lo), 'upper': str(hi)}
        mid = (l+r)/2
        ml, mh = point_bounds(a, mid, bits, order)
        if mh < 0:
            return {'counterpoint': str(mid), 'lower': str(ml), 'upper': str(mh)}
        if depth == max_depth or l == r:
            return None
        lhs = visit(l, mid, depth+1)
        if lhs is None or 'counterpoint' in lhs:
            return lhs
        rhs = visit(mid, r, depth+1)
        if rhs is None or 'counterpoint' in rhs:
            return rhs
        return {'split': str(mid), 'left': lhs, 'right': rhs}
    result = visit(left, right, 0)
    if result is None:
        return None
    if 'counterpoint' in result:
        return {'kind': 'counterpoint-v1', 'domain': [str(left), str(right)],
                'bits': bits, 'order': order, **result}
    return {'kind': 'cover-v1', 'domain': [str(left), str(right)],
            'bits': bits, 'order': order, 'tree': result}
