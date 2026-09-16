"""Optional untrusted conversion to inverse-free Newton certificates."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from .model import PPS, encq
from .search import evaluate, matvec


def compact_enclosure(p: PPS, certificate: dict) -> dict:
    """Replace each inverse by a direction and a positive contraction weight.

    Recheck the result with verify; this producer is not an acceptance gate.
    The full inverse remains a SEARCH choice, not a certificate dependency.
    """
    c=deepcopy(certificate)
    lower=[Q(0)]*p.d
    out=[]
    for step in c['ledger']:
        if step['kind']=='newton':
            inv=[[Q(*v) for v in row] for row in step['inverse']]
            residual=[v-l for v,l in zip(evaluate(p,lower),lower,strict=True)]
            out.append({'kind':'weighted_newton',
                'direction':[encq(x) for x in matvec(inv,residual)],
                'weight':[encq(x) for x in matvec(inv,[Q(1)]*p.d)],
                'next':step['next']})
        else:
            out.append(step)
        lower=[Q(*x) for x in step['next']]
    c['ledger']=out
    return c
