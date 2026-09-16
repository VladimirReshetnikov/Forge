"""Exact rational-series barriers, harmonic minorants, and Cauchy moduli."""
from __future__ import annotations
from fractions import Fraction as Q
from . import algebra as A


def subject(num: A.Poly, den: A.Poly) -> dict:
    return {'numerator': A.enc(num), 'denominator': A.enc(den),
            'interpretation': 'eventual-rational-tail'}

def barrier_residual(num: A.Poly, den: A.Poly, c: int, p: int, C: Q) -> A.Poly:
    u, v = A.power(A.poly([c, 1]), p), A.power(A.poly([c+1, 1]), p)
    return A.sub(A.scale(A.mul(A.sub(v, u), den), C), A.mul(num, A.mul(u, v)))

def synthesize(num: A.Poly, den: A.Poly, start: int = 1) -> dict:
    """Construct a tail certificate using the degree classification.

    The certificate states a conclusion about n >= cutoff. To apply it to an
    arbitrary source sequence, its eventual rational representation is a
    separate obligation. It does not silently define source values at poles.
    """
    num, den = A.poly(num), A.poly(den)
    if not any(num) or num[-1] <= 0 or den[-1] <= 0:
        raise ValueError('this prototype requires positive leading coefficients')
    d = len(den)-len(num)
    if d >= 2:
        p = d-1
        C = num[-1]/(p*den[-1])+1
        residual = barrier_residual(num, den, 0, p, C)
        cutoff = max(1, start, *(A.positive_shift_cutoff(q) for q in (num, den, residual)))
        return make_barrier(num, den, cutoff, 0, p, C)
    c = num[-1]/(2*den[-1]) if d == 1 else Q(1)
    residual = A.sub(A.mul(A.poly([0, 1]), num), A.scale(den, c))
    cutoff = max(1, start, *(A.positive_shift_cutoff(q) for q in (den, residual)))
    return {'kind': 'divergence', 'subject': subject(num, den), 'cutoff': cutoff,
            'minorant': A.text(c), 'shifted_denominator': A.enc(A.shift(den, cutoff)),
            'shifted_residual': A.enc(A.shift(residual, cutoff))}

def make_barrier(num: A.Poly, den: A.Poly, cutoff: int, shift: int, power: int, constant: Q) -> dict:
    residual = barrier_residual(num, den, shift, power, constant)
    return {'kind': 'barrier', 'subject': subject(num, den), 'cutoff': cutoff,
            'shift': shift, 'power': power, 'constant': A.text(constant),
            'shifted_numerator': A.enc(A.shift(num, cutoff)),
            'shifted_denominator': A.enc(A.shift(den, cutoff)),
            'shifted_residual': A.enc(A.shift(residual, cutoff)),
            'tail_bound': A.text(constant/Q(cutoff+shift)**power)}

def optimized_barrier(num: A.Poly, den: A.Poly, cutoff: int,
                      shifts: tuple[int, ...] = (-1, 0, 1),
                      max_power: int = 8) -> dict | None:
    """Solve coefficientwise C*U-V >= 0 as one exact rational interval.

    This is complete for each fixed (cutoff, shift, power), not for all
    nonnegative residual polynomials. No LP package is needed.
    """
    if cutoff < 1 or A.shift(den, cutoff)[0] <= 0:
        return None
    if any(c < 0 for c in A.shift(num, cutoff)) or any(c < 0 for c in A.shift(den, cutoff)):
        return None
    best = None
    for p in range(1, max_power+1):
        for shift in shifts:
            if cutoff+shift < 1:
                continue
            u, v = A.power(A.poly([shift, 1]), p), A.power(A.poly([shift+1, 1]), p)
            U = A.shift(A.mul(A.sub(v, u), den), cutoff)
            V = A.shift(A.mul(num, A.mul(u, v)), cutoff)
            lo, hi, possible = Q(0), None, True
            for i in range(max(len(U), len(V))):
                a = U[i] if i < len(U) else Q(0)
                b = V[i] if i < len(V) else Q(0)
                if a > 0:
                    lo = max(lo, b/a)
                elif a < 0:
                    t = b/a
                    hi = t if hi is None else min(hi, t)
                elif b > 0:
                    possible = False
            C = lo if lo > 0 else (Q(1) if hi is None else min(Q(1), hi/2))
            if not possible or C <= 0 or (hi is not None and C > hi):
                continue
            cert = make_barrier(num, den, cutoff, shift, p, C)
            if best is None or Q(cert['tail_bound']) < Q(best['tail_bound']):
                best = cert
    return best

def modulus(cert: dict, epsilon: Q) -> int:
    if cert['kind'] != 'barrier' or epsilon <= 0:
        raise ValueError('a barrier and a positive epsilon are required')
    C, c, N, p = Q(cert['constant']), cert['shift'], cert['cutoff'], cert['power']
    if (C <= 0 or type(c) is not int or type(N) is not int or N < 1
            or type(p) is not int or not 1 <= p <= 16 or N+c < 1):
        raise ValueError('invalid barrier parameters')
    ratio = C/epsilon
    return max(N, 1-c, ratio.numerator//ratio.denominator+1-c)


def minimal_modulus(cert: dict, epsilon: Q) -> int:
    """Least cutoff >= the certified cutoff satisfying B(k) < epsilon.

    Integer bisection computes floor((floor(C/epsilon))**(1/p)) without
    floating point. The returned index is only a candidate witness: validate
    the barrier and the two rational inequalities before using it as evidence.
    """
    if cert['kind'] != 'barrier' or epsilon <= 0:
        raise ValueError('a barrier and a positive epsilon are required')
    C, c, N, p = Q(cert['constant']), cert['shift'], cert['cutoff'], cert['power']
    if (C <= 0 or type(c) is not int or type(N) is not int or N < 1
            or type(p) is not int or not 1 <= p <= 16 or N+c < 1):
        raise ValueError('invalid barrier parameters')
    r = C/epsilon
    target = r.numerator//r.denominator
    lo, hi = 0, 1
    while hi**p <= target:
        hi *= 2
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**p <= target:
            lo = mid
        else:
            hi = mid
    return max(N, hi-c)
