"""Untrusted bounded discovery. The checker does not import this module."""
from __future__ import annotations
from collections import deque
from fractions import Fraction as F
from itertools import product
from .model import ExpPoly, rat


def make_ladder(f: ExpPoly, order: list[F], terminal_polynomial: bool = True) -> dict | None:
    g, anchors = f, [rat(f.anchor())]
    if f.anchor() < 0:
        return None
    for c in order:
        g = g.step(c)
        if g.anchor() < 0:
            return None
        anchors.append(rat(g.anchor()))
    if g.terms and not (terminal_polynomial and g.positive_polynomial()):
        return None
    return {"kind": "ladder", "cofactors": [rat(c) for c in order],
            "anchors": anchors, "terminal": g.payload()}


def ladder_search(f: ExpPoly, max_states: int = 50000,
                  terminal_polynomial: bool = True) -> dict:
    """BFS in the annihilator-multiplicity grid; minimizes steps if not truncated.

    A certificate found after resource pruning need not be globally shortest.
    Use optimal_ladder for the grammar-relative minimum guarantee.

    Exhaustion of the finite grid means no certificate in this exact grammar,
    not that f has a negative value. Budget exhaustion is separately labelled.
    """
    if type(max_states) is not int or max_states < 1:
        raise ValueError("max_states must be a positive integer")
    rates = tuple(r for r, _ in f.terms)
    caps = tuple(len(p) for _, p in f.terms)
    start = (0,)*len(rates)
    queue = deque([start])
    states = {start: f}
    paths = {start: ()}
    examined = 0
    limited = False
    while queue:
        state = queue.popleft()
        g = states[state]
        examined += 1
        if g.anchor() < 0:
            continue
        if not g.terms or (terminal_polynomial and g.positive_polynomial()):
            cert = make_ladder(f, list(paths[state]), terminal_polynomial)
            return {"status": "certificate", "certificate": cert,
                    "visited": examined, "discovered": len(states), "grid_size": _prod(c+1 for c in caps)}
        for i, c in enumerate(rates):
            if state[i] == caps[i]:
                continue
            child = list(state); child[i] += 1; child = tuple(child)
            if child in states:
                continue
            if len(states) >= max_states:
                limited = True
                continue
            states[child] = g.step(c)
            paths[child] = paths[state] + (c,)
            queue.append(child)
    return {"status": "unknown_budget" if limited else "unknown_grammar",
            "visited": examined, "discovered": len(states), "grid_size": _prod(c+1 for c in caps)}


def _prod(xs):
    out = 1
    for x in xs: out *= x
    return out


def ordered_search(f: ExpPoly, descending: bool = False,
                   terminal_polynomial: bool = True) -> dict | None:
    """Ablation: a single fixed sorted root order, with early stopping."""
    rates = [r for r, p in f.terms for _ in p]
    rates.sort(reverse=descending)
    for n in range(len(rates)+1):
        c = make_ladder(f, rates[:n], terminal_polynomial)
        if c is not None: return c
    return None


def system_search(residuals: list[ExpPoly], diagonal=(-2,-1,0,1,2),
                  off_diagonal=(0,1,2), max_rows: int = 10000) -> dict:
    """Find a constant Metzler matrix, row by row, for supplied residuals.

    Forcing must be a polynomial with nonnegative coefficients on x>=0.
    This is bounded coefficient enumeration, not general positive-system synthesis.
    """
    if not residuals or len(residuals) > 8:
        raise ValueError("one to eight residuals required")
    if any(h.anchor() < 0 for h in residuals):
        return {"status": "unknown_anchor"}
    A, forcing, tries = [], [], 0
    for i, h in enumerate(residuals):
        found = False
        choices = [diagonal if j == i else off_diagonal for j in range(len(residuals))]
        for row in product(*choices):
            tries += 1
            if tries > max_rows:
                return {"status": "unknown_budget", "row_attempts": tries-1}
            b = h.deriv()
            for a, g in zip(row, residuals): b = b - g.scale(a)
            if b.positive_polynomial():
                A.append([rat(F(a)) for a in row])
                forcing.append(b.payload())
                found = True
                break
        if not found:
            return {"status": "unknown_grammar", "row_attempts": tries}
    return {"status": "certificate", "row_attempts": tries,
            "certificate": {"kind": "positive_system", "matrix": A,
                            "forcing": forcing,
                            "anchors": [rat(h.anchor()) for h in residuals]}}


def canonical_search(f: ExpPoly) -> dict:
    """Decide membership in the annihilator-permutation ladder grammar.

    The exchange theorem in the article proves that increasing cofactor order
    dominates every permutation for feasibility. This does NOT decide positivity.
    """
    order=[r for r,p in f.terms for _ in p]
    g=f; used=[]; anchors=[rat(g.anchor())]
    for index in range(len(order)+1):
        if g.anchor()<0:
            return {'status':'no_ladder','certificate':{'kind':'ladder_obstruction',
                    'negative_index':index,'seed':rat(g.anchor())},
                    'steps':index}
        if g.positive_polynomial():
            return {'status':'certificate','certificate':{'kind':'ladder',
                    'cofactors':[rat(c) for c in used],'anchors':anchors,
                    'terminal':g.payload()},'steps':index}
        if index < len(order):
            g=g.step(order[index]); used.append(order[index]); anchors.append(rat(g.anchor()))
    raise ArithmeticError('constructed annihilator did not annihilate the input')


def prove(f: ExpPoly, compression_budget: int = 50000) -> dict:
    """Keep the canonical certificate even if optional shortening runs out."""
    result=canonical_search(f)
    if result['status'] != 'certificate': return result
    shorter=ladder_search(f,max_states=compression_budget)
    result['canonical_steps']=result['steps']
    result['compression_status']=shorter['status']
    if shorter['status']=='certificate':
        candidate=shorter['certificate']
        if len(candidate['cofactors'])<result['steps']:
            result['certificate']=candidate
            result['steps']=len(candidate['cofactors'])
    return result


def _candidate_with_zeros(f: ExpPoly, zeros: int):
    order=sorted([r for r,p in f.terms if r != 0 for _ in p]+[F(0)]*zeros)
    g=f;anchors=[rat(g.anchor())]
    for i in range(len(order)+1):
        if g.anchor()<0:
            return None,{'kind':'negative_anchor','index':i,'value':rat(g.anchor())}
        if i<len(order):
            g=g.step(order[i]);anchors.append(rat(g.anchor()))
    if not g.positive_polynomial():
        for r,p in g.terms:
            if r != 0: raise ArithmeticError('compulsory factors did not eliminate a mode')
            for j,c in enumerate(p):
                if c<0:return None,{'kind':'negative_coefficient','degree':j,'value':rat(c)}
        raise ArithmeticError('unexpected terminal')
    return {'kind':'ladder','cofactors':[rat(c) for c in order],
            'anchors':anchors,'terminal':g.payload()},None


def optimal_ladder(f: ExpPoly) -> dict:
    """Shortest certificate in the input-spectrum, polynomial-terminal grammar.

    Every nonzero mode forces all its annihilator factors. The only free choice
    is the number of zero factors. Feasibility is monotone in this number;
    binary search plus the exchange theorem gives exact optimality.
    """
    initial=canonical_search(f)
    if initial['status']!='certificate':return initial
    maximum=next((len(p) for r,p in f.terms if r==0),0)
    lo,hi=0,maximum;checks=0
    while lo<hi:
        mid=(lo+hi)//2
        c,_=_candidate_with_zeros(f,mid);checks+=1
        if c is None:lo=mid+1
        else:hi=mid
    c,_=_candidate_with_zeros(f,lo);checks+=1
    if c is None:raise ArithmeticError('monotone feasibility invariant failed')
    previous=None
    if lo:
        prev,previous=_candidate_with_zeros(f,lo-1);checks+=1
        if prev is not None:raise ArithmeticError('claimed minimum was not minimal')
    return {'status':'certificate','certificate':c,'canonical_steps':initial['steps'],
            'steps':len(c['cofactors']),'feasibility_checks':checks,
            'minimality':{'kind':'minimum_zero_factors','zeros':lo,'previous_failure':previous}}
