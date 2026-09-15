"""Untrusted numerical/exact search; final acceptance uses poly.py."""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product, combinations
import sympy as sp
import numpy as np
from scipy.optimize import linprog
from .poly import encode, verify_cone, verify_bernstein

def sparse(expr, xs):
    return {m: Q(int(c.p), int(c.q)) for m, c in
            sp.Poly(sp.expand(expr), *xs, domain=sp.QQ).terms() if c}

def monomials(xs, degree):
    for powers in product(range(degree+1), repeat=len(xs)):
        if sum(powers) <= degree:
            yield sp.prod(x**k for x, k in zip(xs, powers))

def quadratic_search(target, xs):
    """Exact rational PSD decomposition of the homogenized quadratic form.

    A positive diagonal pivot yields a weighted square; its Schur complement
    is handled recursively. No square roots or numeric PSD claims are used.
    """
    target = sp.expand(target)
    p = sp.Poly(target, *xs, domain=sp.QQ)
    if p.total_degree() > 2:
        return None
    basis = [sp.Integer(1)] + list(xs)
    q = sp.zeros(len(basis))
    q[0,0] = p.coeff_monomial(1)
    for i,x in enumerate(xs,1):
        q[0,i] = q[i,0] = p.coeff_monomial(x)/2
        q[i,i] = p.coeff_monomial(x*x)
        for j,y in enumerate(xs,1):
            if i < j:
                q[i,j] = q[j,i] = p.coeff_monomial(x*y)/2
    cert = {'nonnegative': [], 'ideal': []}
    active = list(range(len(basis)))
    while active:
        if any(q[i,i] < 0 for i in active):
            return None
        positive = next((i for i in active if q[i,i] > 0),None)
        if positive is None:
            if any(q[i,j] != 0 for i in active for j in active):
                return None
            break
        i = positive; a = q[i,i]
        rest = [j for j in active if j != i]
        form = basis[i] + sum(q[i,j]/a*basis[j] for j in rest)
        cert['nonnegative'].append({'coefficient':str(a),
            'square':encode(sparse(form,xs)), 'factors':[]})
        updated = {(j,k):sp.cancel(q[j,k]-q[j,i]*q[i,k]/a)
                   for j in rest for k in rest}
        for (j,k),v in updated.items():q[j,k]=v
        active=rest
    return cert if verify_cone(sparse(target,xs),[],[],cert,len(xs)) else None

def cone_search(target, xs, inequalities=(), equalities=(), degree=4):
    """Finite rational cone, not a complete SOS or real-closed-field solver.

    Generate monomial/binomial squares and products of at most two input
    inequalities. SciPy selects a support; exact RREF reconstructs weights.
    Numerical failure or a negative exact weight is UNKNOWN, never a proof.
    """
    if degree < 0 or len(xs) == 0:
        raise ValueError('invalid search dimension/degree')
    target = sp.expand(target)
    gs, hs = list(inequalities), list(equalities)
    basis, desc, seen = [], [], set()
    def emit(p, d):
        p = sp.expand(p)
        if p == 0 or sp.Poly(p, *xs).total_degree() > degree:
            return
        key = tuple(sp.Poly(p, *xs).terms())
        if key not in seen:
            seen.add(key); basis.append(p); desc.append(d)
    ms = list(monomials(xs, degree//2))
    squares = ms + [a+s*b for a, b in combinations(ms, 2) for s in (1, -1)]
    for s in squares:
        emit(s*s, ('nn', s, ()))
    factors = [(i,) for i in range(len(gs))] + list(combinations(range(len(gs)), 2))
    for fs in factors:
        g = sp.prod(gs[i] for i in fs)
        for s in ms:
            emit(g*s*s, ('nn', s, fs))
    for i, h in enumerate(hs):
        hd = int(sp.Poly(h, *xs).total_degree()) if h != 0 else 0
        for m in monomials(xs, max(0, degree-hd)):
            for sign in (1, -1):
                emit(sign*m*h, ('ideal', sign*m, i))
    if not basis:
        return None, {'candidates': 0}
    pd = [sp.Poly(p, *xs) for p in basis]
    pt = sp.Poly(target, *xs)
    mons = sorted(set(pt.monoms()).union(*(set(p.monoms()) for p in pd)))
    A = sp.Matrix([[p.coeff_monomial(m) for p in pd] for m in mons])
    b = sp.Matrix([pt.coeff_monomial(m) for m in mons])
    cost = np.array([1 + .001*int(sp.Poly(p, *xs).total_degree()) for p in basis])
    try:
        result = linprog(cost, A_eq=np.array(A, dtype=float), b_eq=np.array(b, dtype=float).ravel(),
                         bounds=(0, None), method='highs')
    except (ValueError, OverflowError, FloatingPointError) as exc:
        return None, {'candidates': len(basis), 'rows': len(mons),
                      'numerical_status': -1, 'reason': type(exc).__name__}
    stats = {'candidates': len(basis), 'rows': len(mons), 'numerical_status': int(result.status)}
    if not result.success:
        return None, stats
    support = [i for i, v in enumerate(result.x) if v > 1e-8]
    if not support:
        weights = []
    else:
        try:
            sol, params = A[:, support].gauss_jordan_solve(b)
            replacements = {v: 0 for v in params}
            weights = [sp.cancel(v.subs(replacements)) for v in sol]
        except ValueError:
            return None, stats
        if any(not w.is_Rational or w < 0 for w in weights):
            return None, stats
    cert = {'nonnegative': [], 'ideal': []}
    for idx, w in zip(support, weights):
        if not w:
            continue
        kind, expr, extra = desc[idx]
        if kind == 'nn':
            cert['nonnegative'].append({'coefficient': str(w), 'square': encode(sparse(expr, xs)),
                                        'factors': list(extra)})
        else:
            cert['ideal'].append({'equality': extra, 'multiplier': encode(sparse(w*expr, xs))})
    ok = verify_cone(sparse(target, xs), [sparse(g, xs) for g in gs],
                     [sparse(h, xs) for h in hs], cert, len(xs))
    stats['support'] = len(cert['nonnegative']) + len(cert['ideal'])
    return (cert if ok else None), stats

def bernstein_search(target, xs, box, max_depth=10, max_nodes=10000):
    """SymPy producer, separate exact sparse checker. Closed rational boxes."""
    target = sp.sympify(target)
    box = [(Q(a), Q(b)) for a, b in box]
    if any(a >= b for a, b in box):
        raise ValueError('box must be nondegenerate')
    stats = {'nodes': 0, 'leaves': 0, 'depth': 0}
    def recur(bx, depth):
        stats['nodes'] += 1; stats['depth'] = max(stats['depth'], depth)
        if stats['nodes'] > max_nodes:
            return None
        sub = {x: sp.Rational(a.numerator, a.denominator) +
               sp.Rational((b-a).numerator, (b-a).denominator)*x
               for x, (a, b) in zip(xs, bx)}
        p = sp.Poly(sp.expand(target.subs(sub, simultaneous=True)), *xs)
        ds = (0,)*len(xs) if p.is_zero else p.degree_list()
        vals = []
        for beta in product(*(range(d+1) for d in ds)):
            c = sum(v * sp.prod(sp.binomial(j, k)/sp.binomial(d, k)
                         for k, j, d in zip(alpha, beta, ds))
                    for alpha, v in p.terms() if all(a <= b for a, b in zip(alpha, beta)))
            vals.append(sp.cancel(c))
        if min(vals) >= 0:
            stats['leaves'] += 1
            return {'kind': 'leaf', 'coefficients': [str(v) for v in vals]}
        if depth >= max_depth:
            return None
        i = depth % len(xs)
        a, b = bx[i]; cut = (a+b)/2
        left, right = list(bx), list(bx)
        left[i], right[i] = (a, cut), (cut, b)
        lc = recur(left, depth+1)
        if lc is None:
            return None
        rc = recur(right, depth+1)
        if rc is None:
            return None
        return {'kind': 'split', 'axis': i, 'cut': str(cut), 'left': lc, 'right': rc}
    cert = recur(box, 0)
    if cert is not None and not verify_bernstein(sparse(target, xs), box, cert, len(xs)):
        raise AssertionError('producer/checker disagreement')
    return cert, stats
