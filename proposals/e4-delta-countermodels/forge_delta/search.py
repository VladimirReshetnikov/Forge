"""Untrusted SymPy search for goal-directed observable closures.

The returned artifacts must be independently replayed by checker.py. No
floating-point computation is used. This is a restricted rational-machine
prototype, not a Lean reifier or tactic.
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from itertools import product
from time import perf_counter
from typing import Any
import sympy as sp

class Limit(Exception):
    pass

@dataclass(frozen=True)
class Limits:
    max_degree: int = 12
    max_basis_per_node: int = 96
    max_work: int = 4000
    max_terms: int = 2048
    max_grid_points: int = 20000


def rat(c: Any) -> list[int]:
    c = sp.Rational(c)
    return [int(c.p), int(c.q)]


def encode(p: Any, variables: tuple) -> list:
    pp=sp.Poly(p,*variables,domain=sp.QQ)
    return [[list(m),rat(c)] for m,c in sorted(pp.terms()) if c]


def decode(raw: list, variables: tuple) -> sp.Expr:
    return sp.Add(*(sp.Rational(*c)*sp.Mul(*(v**a for v,a in zip(variables,m,strict=True)))
                    for m,c in raw))


def machine(n: int, u: int, initial: list, updates: list,
            goals: list, nodes: int=1, root: int=0) -> dict:
    """Build canonical input from expressions in x0,..., and u0,... .

    updates: [(source,destination,label,[update expressions]), ...].
    goals: one list of goal polynomials per control node.
    """
    xs=tuple(sp.symbols(f'x0:{n}')); us=tuple(sp.symbols(f'u0:{u}'))
    return {'version':1,'kind':'polynomial_machine',
            'semantics':'rational-unrestricted-input','state_dim':n,'input_dim':u,
            'nodes':nodes,'initial':{'node':root,'state':[rat(v) for v in initial]},
            'edges':[{'src':s,'dst':d,'label':label,'update':[encode(p,xs+us) for p in fs]}
                     for s,d,label,fs in updates],
            'goals':[[encode(p,xs) for p in gs] for gs in goals]}


class Span:
    """Exact row echelon space, retaining ORIGINAL generators and provenance.

    A pivot row carries coordinates in the original generator list. Search
    certificates never ask a checker to trust this row reduction.
    """
    def __init__(self, xs: tuple):
        self.xs=xs
        self.basis: list[sp.Expr]=[]
        self.origins: list[dict]=[]
        self.rows: dict[tuple,tuple[dict,list]]= {}

    def vector(self,p):
        return {m:c for m,c in sp.Poly(p,*self.xs,domain=sp.QQ).terms() if c}

    def reduce(self,p):
        v=self.vector(p); coeff=[sp.S.Zero]*len(self.basis)
        for pivot,(row,coords) in sorted(self.rows.items(),reverse=True):
            c=v.get(pivot,sp.S.Zero)
            if c:
                for m,a in row.items():
                    v[m]=v.get(m,sp.S.Zero)-c*a
                    if not v[m]: del v[m]
                coeff=[a+c*b for a,b in zip(coeff,coords,strict=True)]
        return v,coeff

    def coordinates(self,p):
        rem,coords=self.reduce(p)
        if rem: raise ValueError('polynomial outside claimed span')
        return coords

    def insert(self,p,origin):
        p=sp.expand(p)
        rem,coords=self.reduce(p)
        if not rem: return None
        pivot=max(rem); lead=rem[pivot]
        for row,oldcoords in self.rows.values(): oldcoords.append(sp.S.Zero)
        newcoords=[-c/lead for c in coords]+[1/lead]
        self.rows[pivot]=({m:c/lead for m,c in rem.items()},newcoords)
        idx=len(self.basis)
        self.basis.append(p);self.origins.append(origin)
        return idx


def input_coefficients(p: Any, xs: tuple, us: tuple) -> dict[tuple,sp.Expr]:
    """Coefficients in arbitrary fresh payloads; no finite sampling."""
    out: dict[tuple,list] = {}
    for m,c in sp.Poly(p,*xs,*us,domain=sp.QQ).terms():
        if c:
            out.setdefault(m[len(xs):],[]).append(c*sp.Mul(*(x**e for x,e in zip(xs,m[:len(xs)],strict=True))))
    return {mu:sp.Add(*terms) for mu,terms in sorted(out.items())}


def solve(problem: dict, limits: Limits=Limits()) -> dict:
    started=perf_counter()
    from .checker import parse_problem, verify_positive, verify_negative
    parse_problem(problem)  # shared schema validation, not shared mathematics
    n=problem['state_dim'];u=problem['input_dim'];q=problem['nodes']
    xs=tuple(sp.symbols(f'x0:{n}'));us=tuple(sp.symbols(f'u0:{u}'))
    root=problem['initial']['node'];initial=[sp.Rational(*v) for v in problem['initial']['state']]
    goals=[[decode(p,xs) for p in gs] for gs in problem['goals']]
    edges=[dict(src=e['src'],dst=e['dst'],update=[decode(p,xs+us) for p in e['update']])
           for e in problem['edges']]
    spans=[Span(xs) for _ in range(q)];agenda=deque()
    incoming=[[] for _ in range(q)]
    for i,e in enumerate(edges): incoming[e['dst']].append(i)
    stats={'coefficient_obligations':0,'pullbacks':0,'grid_points':0}

    def finished(status,cert=None,reason=None):
        stats['basis_dimensions']=[len(s.basis) for s in spans]
        stats['elapsed_seconds']=perf_counter()-started
        result={'status':status,'stats':stats}
        if cert is not None: result['certificate']=cert
        if reason is not None: result['reason']=reason
        return result

    def guard(p):
        pp=sp.Poly(p,*xs,domain=sp.QQ)
        if pp.total_degree()>limits.max_degree: raise Limit('state-degree budget')
        if len(pp.terms())>limits.max_terms: raise Limit('polynomial-term budget')

    def insert(node,p,origin):
        guard(p)
        # Test dependence before charging a new basis slot.
        rem,_=spans[node].reduce(p)
        if not rem: return None
        if len(spans[node].basis)>=limits.max_basis_per_node: raise Limit('basis budget')
        idx=spans[node].insert(p,origin)
        agenda.append((node,idx))
        return idx

    def pull(p,e):
        stats['pullbacks']+=1
        # xreplace is simultaneous: new expressions are not substituted again.
        return sp.expand(p.xreplace(dict(zip(xs,e['update'],strict=True))))

    def counterexample(node,index):
        state=list(initial);steps=[]
        if node!=root: raise ValueError('counterexample must start at initial node')
        while True:
            p=spans[node].basis[index]
            assert p.xreplace(dict(zip(xs,state,strict=True))) != 0
            origin=spans[node].origins[index]
            if origin['kind']=='goal':
                cert={'kind':'execution_counterexample','steps':steps,'goal_index':origin['goal']}
                if not verify_negative(problem,cert): raise Limit('independent execution replay rejected or exceeded size limits')
                return cert
            ei=origin['edge'];e=edges[ei]
            parentnode,parentindex=origin['parent']
            parent=spans[parentnode].basis[parentindex]
            residual=sp.expand(pull(parent,e).xreplace(dict(zip(xs,state,strict=True))))
            if us:
                pp=sp.Poly(residual,*us,domain=sp.QQ)
                ranges=[range(int(pp.degree(v))+1) for v in us]
            else: ranges=[]
            chosen=None
            for point in product(*ranges):
                stats['grid_points']+=1
                if stats['grid_points']>limits.max_grid_points: raise Limit('counterexample-grid budget')
                val=residual.xreplace(dict(zip(us,point,strict=True)))
                if val!=0:
                    chosen=point;break
            if chosen is None: raise AssertionError('nonzero coefficient has no grid witness')
            env=dict(zip(xs+us,tuple(state)+chosen,strict=True))
            state=[sp.expand(f.xreplace(env)) for f in e['update']]
            steps.append({'edge':ei,'input':[rat(v) for v in chosen]})
            node,index=parentnode,parentindex

    try:
        for node,gs in enumerate(goals):
            for gi,g in enumerate(gs): insert(node,g,{'kind':'goal','goal':gi})
        while agenda:
            node,idx=agenda.popleft()
            p=spans[node].basis[idx]
            if node==root and p.xreplace(dict(zip(xs,initial,strict=True))) != 0:
                return finished('refuted',counterexample(node,idx))
            for ei in incoming[node]:
                e=edges[ei]
                for mu,c in input_coefficients(pull(p,e),xs,us).items():
                    stats['coefficient_obligations']+=1
                    if stats['coefficient_obligations']>limits.max_work: raise Limit('work budget')
                    insert(e['src'],c,{'kind':'coefficient','edge':ei,
                                     'parent':[node,idx],'input_exponent':list(mu)})
        cert={'kind':'observable_closure',
              'basis':[[encode(p,xs) for p in s.basis] for s in spans],
              'goal_coordinates':[[[rat(c) for c in spans[node].coordinates(g)] for g in gs]
                                  for node,gs in enumerate(goals)],
              'edge_coordinates':[]}
        for e in edges:
            rows=[]
            for p in spans[e['dst']].basis:
                rows.append([{'input_exponent':list(mu),
                              'coordinates':[rat(c) for c in spans[e['src']].coordinates(cpoly)]}
                             for mu,cpoly in input_coefficients(pull(p,e),xs,us).items()])
            cert['edge_coordinates'].append(rows)
        if not verify_positive(problem,cert):
            return finished('unknown',reason='independent closure replay rejected or exceeded size limits')
        return finished('proved',cert)
    except Limit as exc:
        return finished('unknown',reason=str(exc))


def conserved_target_only(problem: dict) -> bool:
    """Deliberately narrow ablation, NOT a grind/Lean emulation.

    Single-node problems only. Each requested target itself must be conserved.
    """
    if problem['nodes']!=1: return False
    n=problem['state_dim'];u=problem['input_dim']
    xs=tuple(sp.symbols(f'x0:{n}'));us=tuple(sp.symbols(f'u0:{u}'))
    init=[sp.Rational(*v) for v in problem['initial']['state']]
    for raw in problem['goals'][0]:
        g=decode(raw,xs)
        if g.xreplace(dict(zip(xs,init,strict=True)))!=0:return False
        for e in problem['edges']:
            fs=[decode(v,xs+us) for v in e['update']]
            if sp.expand(g.xreplace(dict(zip(xs,fs,strict=True)))-g)!=0:return False
    return True
