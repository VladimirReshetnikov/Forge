"""Search-independent exact replay. Uses Python's standard library only.

This checker is not formally verified. Its acceptance is NOT a Lean proof.
Problems are supplied separately from certificates; certificate data cannot
choose a weaker target or omit an edge. All updates are simultaneous.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import gcd
import json
from pathlib import Path
from typing import Any

Poly = dict[tuple[int, ...], Q]
MAX_TERMS = 20000
MAX_BITS = 4096

class Invalid(ValueError):
    """Malformed certificate, resource limit, or failed mathematical check."""

def require(p: bool, msg: str) -> None:
    if not p:
        raise Invalid(msg)

def keys(obj: Any, expected: set[str]) -> None:
    require(type(obj) is dict and set(obj) == expected, 'unexpected/missing fields')

def integer(x: Any, lo: int, hi: int) -> int:
    require(type(x) is int and lo <= x <= hi, 'invalid integer')
    return x

def rational(x: Any) -> Q:
    require(type(x) is list and len(x) == 2, 'rational must be [numerator,denominator]')
    n, d = x
    require(type(n) is int and type(d) is int and d > 0, 'invalid rational fields')
    require(n.bit_length() <= MAX_BITS and d.bit_length() <= MAX_BITS, 'rational too large')
    require(gcd(n, d) == 1, 'rational not reduced')
    return Q(n, d)

def checked(p: Poly) -> Poly:
    p = {m:c for m,c in p.items() if c}
    require(len(p) <= MAX_TERMS, 'polynomial term budget exceeded')
    require(all(c.numerator.bit_length() <= MAX_BITS and c.denominator.bit_length() <= MAX_BITS
                for c in p.values()), 'coefficient budget exceeded')
    return p

def polynomial(raw: Any, n: int) -> Poly:
    require(type(raw) is list and len(raw) <= 2048, 'invalid polynomial')
    out: Poly = {}
    prev = None
    for term in raw:
        require(type(term) is list and len(term) == 2, 'invalid term')
        exps, coeff = term
        require(type(exps) is list and len(exps) == n, 'exponent dimension')
        m = tuple(integer(a, 0, 64) for a in exps)
        require(sum(m) <= 64, 'degree budget')
        require(prev is None or prev < m, 'terms must be sorted and distinct')
        c = rational(coeff)
        require(c != 0, 'explicit zero coefficient')
        out[m] = c
        prev = m
    return out

def constant(c: Q | int, n: int) -> Poly:
    return {} if c == 0 else {(0,)*n:Q(c)}

def add(a: Poly, b: Poly) -> Poly:
    r = dict(a)
    for m,c in b.items():
        r[m] = r.get(m, Q(0)) + c
    return checked(r)

def scale(a: Poly, c: Q) -> Poly:
    return checked({m:c*v for m,v in a.items()})

def mul(a: Poly, b: Poly) -> Poly:
    r: Poly = {}
    for m,c in a.items():
        for n,d in b.items():
            k = tuple(x+y for x,y in zip(m,n,strict=True))
            r[k] = r.get(k,Q(0)) + c*d
        require(len(r) <= MAX_TERMS, 'multiplication term budget')
    return checked(r)

def power(a: Poly, k: int, n: int) -> Poly:
    r = constant(1,n)
    while k:
        if k & 1:
            r = mul(r,a)
        k >>= 1
        if k:
            a = mul(a,a)
    return r

def substitute(p: Poly, images: list[Poly], n: int) -> Poly:
    """Simultaneous polynomial substitution into n target variables."""
    r: Poly = {}
    cache: dict[tuple[int,int],Poly] = {}
    for m,c in p.items():
        require(len(m) == len(images), 'substitution arity')
        term = constant(c,n)
        for i,k in enumerate(m):
            if k:
                if (i,k) not in cache:
                    cache[i,k] = power(images[i],k,n)
                term = mul(term,cache[i,k])
        r = add(r,term)
    return r

def evaluate(p: Poly, values: list[Q]) -> Q:
    total = Q(0)
    for m,c in p.items():
        require(len(m) == len(values), 'evaluation arity')
        v = c
        for x,k in zip(values,m,strict=True):
            v *= x**k
        total += v
    require(total.numerator.bit_length() <= MAX_BITS and total.denominator.bit_length() <= MAX_BITS,
            'evaluation coefficient budget')
    return total

def lift(p: Poly, extra: int) -> Poly:
    return {m+(0,)*extra:c for m,c in p.items()}

def parse_problem(p: Any) -> tuple[int,int,int,int,list[Q],list[dict],list[list[Poly]]]:
    keys(p,{'version','kind','semantics','state_dim','input_dim','nodes','initial','edges','goals'})
    require(p['version'] == 1 and type(p['version']) is int, 'version')
    require(p['kind'] == 'polynomial_machine' and p['semantics'] == 'rational-unrestricted-input',
            'unsupported semantics')
    n = integer(p['state_dim'],1,16)
    u = integer(p['input_dim'],0,3)
    q = integer(p['nodes'],1,16)
    keys(p['initial'],{'node','state'})
    root = integer(p['initial']['node'],0,q-1)
    require(type(p['initial']['state']) is list and len(p['initial']['state']) == n, 'initial arity')
    initial = [rational(v) for v in p['initial']['state']]
    require(type(p['edges']) is list and len(p['edges']) <= 64, 'edge bound')
    edges = []
    for edge in p['edges']:
        keys(edge,{'src','dst','label','update'})
        src = integer(edge['src'],0,q-1)
        dst = integer(edge['dst'],0,q-1)
        require(type(edge['label']) is str and len(edge['label']) <= 128, 'edge label')
        require(type(edge['update']) is list and len(edge['update']) == n, 'update arity')
        edges.append({'src':src,'dst':dst,'update':[polynomial(v,n+u) for v in edge['update']]})
    require(type(p['goals']) is list and len(p['goals']) == q, 'goal nodes')
    goals=[]
    for gs in p['goals']:
        require(type(gs) is list and len(gs) <= 16, 'goals per node')
        goals.append([polynomial(g,n) for g in gs])
    return n,u,q,root,initial,edges,goals

def _positive(problem: Any, cert: Any) -> None:
    n,u,q,root,initial,edges,goals = parse_problem(problem)
    keys(cert,{'kind','basis','goal_coordinates','edge_coordinates'})
    require(cert['kind'] == 'observable_closure', 'certificate kind')
    require(type(cert['basis']) is list and len(cert['basis']) == q, 'basis nodes')
    basis=[]
    for bs in cert['basis']:
        require(type(bs) is list and len(bs) <= 128, 'basis bound')
        basis.append([polynomial(p,n) for p in bs])
    # Independence/minimality is unnecessary for soundness.
    for p in basis[root]:
        require(evaluate(p,initial) == 0, 'initial obligation failed')
    gc = cert['goal_coordinates']
    require(type(gc) is list and len(gc) == q, 'goal coordinates nodes')
    for node in range(q):
        require(type(gc[node]) is list and len(gc[node]) == len(goals[node]), 'goal coordinate count')
        for goal, coords in zip(goals[node],gc[node],strict=True):
            require(type(coords) is list and len(coords) == len(basis[node]), 'goal coordinate arity')
            rhs: Poly = {}
            for p,c in zip(basis[node],coords,strict=True):
                rhs=add(rhs,scale(p,rational(c)))
            require(goal == rhs, 'goal identity failed')
    ec = cert['edge_coordinates']
    require(type(ec) is list and len(ec) == len(edges), 'edge coverage failed')
    for edge,rows in zip(edges,ec,strict=True):
        src,dst=edge['src'],edge['dst']
        require(type(rows) is list and len(rows) == len(basis[dst]), 'edge row coverage failed')
        for target,entries in zip(basis[dst],rows,strict=True):
            require(type(entries) is list and len(entries) <= 2048, 'coefficient rows')
            lhs=substitute(target,edge['update'],n+u)
            rhs: Poly={}
            prev=None
            for entry in entries:
                keys(entry,{'input_exponent','coordinates'})
                raw=entry['input_exponent']
                require(type(raw) is list and len(raw) == u, 'payload exponent arity')
                mu=tuple(integer(v,0,64) for v in raw)
                require(prev is None or prev < mu, 'coefficient exponents sorted/distinct')
                prev=mu
                cs=entry['coordinates']
                require(type(cs) is list and len(cs) == len(basis[src]), 'edge coordinate arity')
                for p,c in zip(basis[src],cs,strict=True):
                    c=rational(c)
                    rhs=add(rhs,{m+mu:c*v for m,v in p.items()})
            require(lhs == rhs, 'edge polynomial identity failed')

def _negative(problem: Any, cert: Any) -> None:
    n,u,q,node,state,edges,goals=parse_problem(problem)
    keys(cert,{'kind','steps','goal_index'})
    require(cert['kind'] == 'execution_counterexample', 'counterexample kind')
    require(type(cert['steps']) is list and len(cert['steps']) <= 1024, 'trace bound')
    for step in cert['steps']:
        keys(step,{'edge','input'})
        index=integer(step['edge'],0,len(edges)-1)
        edge=edges[index]
        require(edge['src'] == node, 'trace control-flow mismatch')
        require(type(step['input']) is list and len(step['input']) == u, 'input arity')
        inp=[rational(v) for v in step['input']]
        state=[evaluate(p,state+inp) for p in edge['update']]
        node=edge['dst']
    idx=integer(cert['goal_index'],0,len(goals[node])-1)
    require(evaluate(goals[node][idx],state) != 0, 'trace is not a counterexample')

def verify_positive(problem: Any, cert: Any) -> bool:
    try:
        _positive(problem,cert)
        return True
    except (Invalid, TypeError, ValueError, KeyError, IndexError, OverflowError, RecursionError):
        return False

def verify_negative(problem: Any, cert: Any) -> bool:
    try:
        _negative(problem,cert)
        return True
    except (Invalid, TypeError, ValueError, KeyError, IndexError, OverflowError, RecursionError):
        return False

def load_json(path: str | Path) -> Any:
    data=Path(path).read_bytes()
    require(len(data) <= 16_000_000, 'file size bound')
    def pairs(xs):
        out={}
        for k,v in xs:
            require(k not in out,'duplicate JSON key')
            out[k]=v
        return out
    def no_float(x):
        raise Invalid('floating-point JSON values prohibited')
    return json.loads(data,object_pairs_hook=pairs,parse_float=no_float,parse_constant=no_float)
