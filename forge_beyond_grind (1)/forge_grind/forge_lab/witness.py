"""Small typed polynomial-witness synthesis with universal exact certification.

Samples reject candidates only. A result is accepted only after certificates for
both polynomial inequalities have been independently checked.
"""
from fractions import Fraction as Q
from itertools import product
from time import perf_counter
from .poly import Poly, check_cone
from .nonlinear import cone_search


def synthesize_majorant():
    """Prove forall real x, exists y, y >= x and y >= -x in a tiny grammar."""
    start = perf_counter()
    x = Poly.var(1, 0)
    coeffs = sorted(product(range(-2, 3), repeat=3),
                    key=lambda c: (sum(abs(a) for a in c), c))
    samples = tuple(map(Q, (-2, -1, 0, 1, 2)))
    survivors = 0
    for i, (a, b, c) in enumerate(coeffs, 1):
        w = a + b*x + c*x**2
        if any(w.eval((t,)) < abs(t) for t in samples):
            continue
        survivors += 1
        c1, _ = cone_search(w-x)
        c2, _ = cone_search(w+x)
        if c1 is not None and c2 is not None and check_cone(w-x, (), c1) and check_cone(w+x, (), c2):
            return w, (c1, c2), {
                'status': 'certified', 'candidate_count': i,
                'sample_count': len(samples), 'sample_survivors': survivors,
                'witness': str(w), 'seconds': perf_counter()-start}
    return None, None, {'status': 'no_certificate', 'candidate_count': len(coeffs),
                        'sample_survivors': survivors, 'seconds': perf_counter()-start}
