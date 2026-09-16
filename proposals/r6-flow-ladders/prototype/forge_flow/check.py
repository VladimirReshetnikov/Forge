"""Replay using a separate sparse representation. Imports no search code.

The algebra checker is research Python, not a Lean kernel or verified program.
Analytic soundness additionally uses the theorems proved in the accompanying paper.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import gcd

MAX_BITS = 16384
MAX_TERMS = 512
MAX_DEGREE = 256
MAX_STEPS = 512


def fraction(x) -> F:
    if not isinstance(x, list) or len(x) != 2 or any(type(a) is not int for a in x):
        raise ValueError("rational must be an integer pair")
    p, q = x
    if q <= 0 or gcd(p, q) != 1:
        raise ValueError("rational is not reduced with positive denominator")
    if max(abs(p).bit_length(), q.bit_length()) > MAX_BITS:
        raise ValueError("rational exceeds resource cap")
    return F(p, q)


def decode(terms) -> dict[tuple[F, int], F]:
    if not isinstance(terms, list) or len(terms) > MAX_TERMS:
        raise ValueError("bad term array")
    out = {}; last = None
    for t in terms:
        if type(t) is not dict or set(t) != {"rate", "coeffs"}:
            raise ValueError("bad exponential term")
        r = fraction(t['rate']); cs = t['coeffs']
        if last is not None and r <= last:
            raise ValueError("rates must be strictly increasing")
        last = r
        if not isinstance(cs, list) or not 1 <= len(cs) <= MAX_DEGREE+1:
            raise ValueError("bad coefficient array")
        a = list(map(fraction, cs))
        if a[-1] == 0: raise ValueError("trailing zero")
        for j, c in enumerate(a):
            if c: out[(r, j)] = c
    return out


def add(a, b, scale=F(1)):
    z = dict(a)
    for key, value in b.items():
        z[key] = z.get(key, F(0)) + scale*value
        if not z[key]: del z[key]
    return z


def derivative(a):
    z = {}
    for (r, j), c in a.items():
        if r: z[(r, j)] = z.get((r, j), F(0)) + r*c
        if j: z[(r, j-1)] = z.get((r, j-1), F(0)) + j*c
    return {k: v for k,v in z.items() if v}


def anchor(a):
    return sum((c for (_, j), c in a.items() if j == 0), F(0))


def positive_polynomial(a):
    return all(r == 0 and c >= 0 for (r, _), c in a.items())


def checked_problem(problem):
    if type(problem) is not dict or set(problem) != {'kind','anchor','direction','terms'}:
        raise ValueError("bad external problem")
    if problem['kind'] != 'exp_poly_nonnegative' or problem['anchor'] != [0,1] or problem['direction'] != 'right':
        raise ValueError("unsupported source domain")
    return decode(problem['terms'])


def check_ladder(problem, certificate) -> bool:
    try:
        g = checked_problem(problem)
        if set(certificate) != {'kind','cofactors','anchors','terminal'} or certificate['kind'] != 'ladder': return False
        cs = certificate['cofactors']; seeds = certificate['anchors']
        if not isinstance(cs,list) or len(cs)>MAX_STEPS or not isinstance(seeds,list) or len(seeds)!=len(cs)+1: return False
        for i in range(len(cs)+1):
            v = anchor(g)
            if v != fraction(seeds[i]) or v < 0: return False
            if i < len(cs):
                g = add(derivative(g), g, -fraction(cs[i]))
        return g == decode(certificate['terminal']) and positive_polynomial(g)
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False


def check_system(problems, certificate) -> bool:
    try:
        H = [checked_problem(p) for p in problems]
        n = len(H)
        if not 1 <= n <= 8: return False
        if set(certificate) != {'kind','matrix','forcing','anchors'} or certificate['kind'] != 'positive_system': return False
        rows = certificate['matrix']; bs = certificate['forcing']; seeds = certificate['anchors']
        if not len(rows)==len(bs)==len(seeds)==n: return False
        for i in range(n):
            if len(rows[i]) != n or fraction(seeds[i]) != anchor(H[i]) or anchor(H[i]) < 0: return False
            a = [fraction(c) for c in rows[i]]
            if any(a[j] < 0 for j in range(n) if j != i): return False
            rhs = decode(bs[i])
            if not positive_polynomial(rhs): return False
            for j in range(n): rhs = add(rhs,H[j],a[j])
            if derivative(H[i]) != rhs: return False
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False


def check_obstruction(problem, cert) -> bool:
    """No ladder in the declared permutation grammar, NOT a disproof of f>=0."""
    try:
        g=checked_problem(problem)
        if set(cert)!={'kind','negative_index','seed'} or cert['kind']!='ladder_obstruction': return False
        counts={}
        for r,j in g: counts[r]=max(counts.get(r,0),j+1)
        order=[r for r in sorted(counts) for _ in range(counts[r])]
        index=cert['negative_index']
        if type(index) is not int or not 0<=index<=len(order): return False
        for c in order[:index]:
            if anchor(g)<0: return False
            g=add(derivative(g),g,-c)
        return anchor(g)<0 and anchor(g)==fraction(cert['seed'])
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,OverflowError): return False


def check_minimality(problem, ladder, receipt) -> bool:
    """Check the finite-grammar minimality receipt, using the paper's theorem."""
    try:
        if not check_ladder(problem,ladder):return False
        if set(receipt)!={'kind','zeros','previous_failure'} or receipt['kind']!='minimum_zero_factors':return False
        g=checked_problem(problem);counts={}
        for r,j in g:counts[r]=max(counts.get(r,0),j+1)
        z=receipt['zeros'];cap=counts.get(F(0),0)
        if type(z) is not int or not 0<=z<=cap:return False
        forced=[r for r in sorted(counts) if r!=0 for _ in range(counts[r])]
        actual=[fraction(c) for c in ladder['cofactors']]
        if sorted(actual)!=sorted(forced+[F(0)]*z):return False
        if z==0:return receipt['previous_failure'] is None
        prev=receipt['previous_failure'];order=sorted(forced+[F(0)]*(z-1))
        kind=prev.get('kind')
        if kind=='negative_anchor':
            if set(prev)!={'kind','index','value'}:return False
            idx=prev['index']
            if type(idx) is not int or not 0<=idx<=len(order):return False
            for c in order[:idx]:g=add(derivative(g),g,-c)
            return anchor(g)<0 and fraction(prev['value'])==anchor(g)
        if kind=='negative_coefficient':
            if set(prev)!={'kind','degree','value'}:return False
            d=prev['degree']
            if type(d) is not int or d<0:return False
            for c in order:g=add(derivative(g),g,-c)
            if any(r!=0 for r,_ in g):return False
            v=g.get((F(0),d),F(0))
            return v<0 and fraction(prev['value'])==v
        return False
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,OverflowError):return False
