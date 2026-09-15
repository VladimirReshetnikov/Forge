"""Polynomial majorant witnesses, certified by exact cone replay.

PROVENANCE: p9-proof-planner/forge_lab/witness.py, unique to p9, retargeted onto
forge/cone.py (p9's own nonlinear.py duplicated the cone search) and onto the
merged exact checker in forge/certificates.py.

Samples reject candidates only. A result is accepted solely after certificates
for BOTH polynomial inequalities have been independently checked.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from time import perf_counter
from ..poly import Poly
from ..certificates import check_cone
from ..cone import discover


def synthesize_majorant(*, degree: int = 2, bound: int = 2):
    """Prove: for all real x there is a term w(x) with w >= x and w >= -x."""
    start = perf_counter()
    x = Poly.var(1, 0)
    coeffs = sorted(product(range(-bound, bound + 1), repeat=3),
                    key=lambda c: (sum(abs(a) for a in c), c))
    samples = tuple(map(Q, (-2, -1, 0, 1, 2)))
    survivors = 0
    for i, (a, b, c) in enumerate(coeffs, 1):
        w = a + b * x + c * x ** 2
        if any(w.evaluate((t,)) < abs(t) for t in samples):
            continue
        survivors += 1
        r1 = discover(w - x, degree=degree)
        r2 = discover(w + x, degree=degree)
        c1, c2 = r1.certificate, r2.certificate
        if (c1 is not None and c2 is not None
                and check_cone(w - x, (), (), c1) and check_cone(w + x, (), (), c2)):
            return w, (c1, c2), {
                'status': 'certified', 'candidate_count': i,
                'sample_count': len(samples), 'sample_survivors': survivors,
                'witness': str(w), 'seconds': perf_counter() - start}
    return None, None, {'status': 'no_certificate', 'candidate_count': len(coeffs),
                        'sample_survivors': survivors, 'seconds': perf_counter() - start}
