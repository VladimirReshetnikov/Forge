"""Integrating-factor ladder synthesis for rational exponential polynomials."""
from __future__ import annotations
from collections import deque
from fractions import Fraction as Q
from . import algebra as A

ExpPoly = dict[Q, A.Poly]

def clean(f: ExpPoly) -> ExpPoly:
    return {Q(a): A.poly(p) for a, p in f.items() if any(p)}

def encode(f: ExpPoly) -> list:
    return [[A.text(a), A.enc(p)] for a, p in sorted(clean(f).items())]

def decode(xs: list) -> ExpPoly:
    return clean({Q(a): A.dec(p) for a, p in xs})

def seed(f: ExpPoly) -> Q:
    return sum((p[0] for p in f.values()), Q(0))

def apply(f: ExpPoly, rate: Q) -> ExpPoly:
    return clean({a: A.add(A.deriv(p), A.scale(p, a-rate)) for a, p in f.items()})

def terminal(f: ExpPoly) -> bool:
    return all(c >= 0 for p in f.values() for c in p)

def search(f: ExpPoly, max_depth: int = 12, max_nodes: int = 4000) -> dict | None:
    f = clean(f)
    subject = {'exp_poly': encode(f), 'domain': 'x>=0'}
    if seed(f) < 0:
        return None
    rates = sorted(set(f) | {Q(0)})
    queue = deque([(f, [], [f])])
    seen = {repr(encode(f))}
    visits = 0
    while queue and visits < max_nodes:
        current, path, stages = queue.popleft()
        visits += 1
        if terminal(current):
            return {'kind': 'ladder', 'subject': subject,
                    'rates': [A.text(a) for a in path],
                    'stages': [encode(g) for g in stages],
                    'seeds': [A.text(seed(g)) for g in stages],
                    'search_nodes': visits}
        if len(path) >= max_depth:
            continue
        for a in rates:
            g = apply(current, a)
            key = repr(encode(g))
            if seed(g) >= 0 and key not in seen:
                seen.add(key)
                queue.append((g, path+[a], stages+[g]))
    return None

def lift(g: ExpPoly, rate: Q, initial: Q) -> ExpPoly:
    """Construct exact f with (D-rate)f=g and f(0)=initial.

    Used only for a clearly labelled planted-certificate test family.
    """
    out: ExpPoly = {}
    for a, p in g.items():
        if a == rate:
            out[a] = A.poly([0] + [p[i]/(i+1) for i in range(len(p))])
        else:
            d = a-rate
            q = [Q(0)]*len(p)
            for i in range(len(p)-1, -1, -1):
                q[i] = (p[i] - ((i+1)*q[i+1] if i+1 < len(p) else 0))/d
            out[a] = A.poly(q)
    correction = initial-seed(out)
    out[rate] = A.add(out.get(rate, A.poly([0])), A.poly([correction]))
    return clean(out)
