#!/usr/bin/env python3
"""Independent exact checker for Forge relational-closure research certificates.

Only the Python standard library is imported. This is NOT a Lean proof checker.
Search and this checker share a documented JSON schema, not polynomial code.
The original problem is a separate, mandatory argument; the certificate cannot
choose its target, transitions, initial states, or variable domains.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import re
import sys
from typing import Any

SCHEMA = 'forge-polynomial-system-v1'
MAX_BYTES = 8_000_000
MAX_TERMS = 4000
MAX_BITS = 8192
MAX_OPS = 3_000_000

class Rejected(ValueError):
    pass

class BudgetExceeded(Rejected):
    pass

class Arithmetic:
    def __init__(self, limit: int = MAX_OPS):
        self.operations = 0
        self.limit = limit

    def charge(self, n: int = 1) -> None:
        self.operations += n
        if self.operations > self.limit:
            raise BudgetExceeded('checker arithmetic-operation limit')

    def clean(self, p: dict) -> dict:
        q = {m:c for m,c in p.items() if c}
        if len(q) > MAX_TERMS:
            raise BudgetExceeded('expanded polynomial too large')
        for m,c in q.items():
            if max(c.numerator.bit_length(), c.denominator.bit_length()) > MAX_BITS:
                raise BudgetExceeded('expanded coefficient too large')
            if sum(m) > 256:
                raise BudgetExceeded('expanded degree too large')
        return q

    def add(self, p: dict, q: dict) -> dict:
        out = p.copy()
        self.charge(len(q))
        for m,c in q.items():
            out[m] = out.get(m, Fraction(0)) + c
        return self.clean(out)

    def mul(self, p: dict, q: dict) -> dict:
        self.charge(len(p)*len(q))
        out: dict = {}
        for m,c in p.items():
            for n,d in q.items():
                e = tuple(a+b for a,b in zip(m,n,strict=True))
                out[e] = out.get(e,Fraction(0)) + c*d
        return self.clean(out)

    def power(self, p: dict, k: int, n: int) -> dict:
        ans = {(0,)*n:Fraction(1)}
        while k:
            if k & 1:
                ans = self.mul(ans,p)
            k //= 2
            if k:
                p = self.mul(p,p)
        return ans

    def substitute(self, p: dict, images: list[dict], n: int) -> dict:
        out: dict = {}
        for m,c in p.items():
            if len(m) != len(images):
                raise Rejected('substitution arity')
            term = {(0,)*n:c}
            for image,k in zip(images,m,strict=True):
                if k:
                    term = self.mul(term,self.power(image,k,n))
            out = self.add(out,term)
        return out

    def evaluate(self, p: dict, values: list[Fraction]) -> Fraction:
        ans = Fraction(0)
        for m,c in p.items():
            self.charge(1+len(m))
            if len(m) != len(values):
                raise Rejected('evaluation arity')
            for x,k in zip(values,m,strict=True):
                c *= x**k
            ans += c
        if max(ans.numerator.bit_length(),ans.denominator.bit_length()) > MAX_BITS:
            raise BudgetExceeded('evaluation result too large')
        return ans


def integer(x: Any, lo: int, hi: int, what: str) -> int:
    if type(x) is not int or not lo <= x <= hi:
        raise Rejected(what)
    return x


def keys(x: Any, expected: set[str], what: str) -> None:
    if type(x) is not dict or set(x) != expected:
        raise Rejected(what+' keys')


def array(x: Any, maximum: int, what: str, length: int | None = None) -> list:
    if type(x) is not list or len(x) > maximum or (length is not None and len(x) != length):
        raise Rejected(what+' length/type')
    return x


def rational(x: Any) -> Fraction:
    array(x,2,'rational',2)
    if any(type(s) is not str or len(s)>2500 for s in x):
        raise Rejected('rational components must be bounded strings')
    if not re.fullmatch(r'-?(0|[1-9][0-9]*)',x[0]) or not re.fullmatch(r'[1-9][0-9]*',x[1]):
        raise Rejected('rational spelling')
    a,b = int(x[0]),int(x[1])
    if max(a.bit_length(),b.bit_length())>MAX_BITS or math.gcd(a,b)!=1 or x[0]=='-0':
        raise Rejected('noncanonical or oversized rational')
    return Fraction(a,b)


def polynomial(x: Any, n: int) -> dict:
    terms = array(x,MAX_TERMS,'polynomial')
    out = {}
    previous = None
    for row in terms:
        array(row,2,'term',2)
        m = tuple(integer(e,0,128,'exponent') for e in array(row[0],32,'exponents',n))
        if sum(m)>128:
            raise Rejected('input polynomial degree')
        c = rational(row[1])
        if not c or (previous is not None and m <= previous):
            raise Rejected('zero, duplicate, or unsorted term')
        out[m] = c
        previous = m
    return out


def embed(p: dict, extra: int) -> dict:
    return {m+(0,)*extra:c for m,c in p.items()}


def parse_problem(raw: dict) -> dict:
    keys(raw,{'schema','name','n','locations','parameters','initial','edges','targets'},'problem')
    if raw['schema'] != SCHEMA or type(raw['name']) is not str:
        raise Rejected('problem schema/name')
    n = integer(raw['n'],1,16,'state dimension')
    L = integer(raw['locations'],1,32,'locations')
    r = integer(raw['parameters'],0,8,'parameters')
    initial = []
    for b in array(raw['initial'],32,'initial'):
        keys(b,{'location','state'},'initial')
        loc = integer(b['location'],0,L-1,'initial location')
        state = [polynomial(p,r) for p in array(b['state'],16,'initial state',n)]
        initial.append((loc,state))
    edges = []
    for e in array(raw['edges'],128,'edges'):
        keys(e,{'src','dst','inputs','update'},'edge')
        src = integer(e['src'],0,L-1,'edge source')
        dst = integer(e['dst'],0,L-1,'edge destination')
        u = integer(e['inputs'],0,8,'edge inputs')
        update = [polynomial(p,n+u) for p in array(e['update'],16,'update',n)]
        edges.append((src,dst,u,update))
    targets=[]
    for t in array(raw['targets'],32,'targets'):
        keys(t,{'location','polynomial'},'target')
        targets.append((integer(t['location'],0,L-1,'target location'),polynomial(t['polynomial'],n)))
    if not initial or not targets:
        raise Rejected('nonempty initial and target lists required')
    return dict(n=n,L=L,r=r,initial=initial,edges=edges,targets=targets)


def check_certificate(original: dict, raw: dict, *, operation_limit: int = MAX_OPS) -> dict:
    P = parse_problem(original)
    keys(raw,{'schema','basis','target','step'},'certificate')
    if raw['schema']!='forge-closure-cert-v1':
        raise Rejected('certificate schema')
    n,L = P['n'],P['L']
    A = Arithmetic(operation_limit)
    B = [[polynomial(q,n) for q in array(row,128,'basis at location')]
         for row in array(raw['basis'],32,'basis',L)]
    if sum(map(len,B))>512:
        raise Rejected('too many basis polynomials')
    for loc,initial in P['initial']:
        for g in B[loc]:
            if A.substitute(g,initial,P['r']):
                raise Rejected('initial identity is nonzero')
    for (loc,p),row in zip(P['targets'],array(raw['target'],32,'target multipliers',len(P['targets'])),strict=True):
        multipliers = [polynomial(q,n) for q in array(row,128,'target row',len(B[loc]))]
        rhs = {}
        for h,g in zip(multipliers,B[loc],strict=True):
            rhs=A.add(rhs,A.mul(h,g))
        if rhs!=p:
            raise Rejected('target identity is nonzero')
    for edge,rows in zip(P['edges'],array(raw['step'],128,'step matrices',len(P['edges'])),strict=True):
        src,dst,u,F = edge
        rows=array(rows,128,'step rows',len(B[dst]))
        for g,row in zip(B[dst],rows,strict=True):
            hs=[polynomial(h,n+u) for h in array(row,128,'step columns',len(B[src]))]
            lhs=A.substitute(g,F,n+u)
            rhs={}
            for h,q in zip(hs,B[src],strict=True):
                rhs=A.add(rhs,A.mul(h,embed(q,u)))
            if lhs!=rhs:
                raise Rejected('transition identity is nonzero')
    return {'accepted':True,'kind':'closure-certificate','arithmetic_operations':A.operations,
            'basis_dimensions':list(map(len,B))}


def check_counterexample(original: dict, raw: dict, *, operation_limit: int = MAX_OPS) -> dict:
    P=parse_problem(original)
    keys(raw,{'schema','initial','parameters','steps','target'},'counterexample')
    if raw['schema']!='forge-counterexample-v1':
        raise Rejected('counterexample schema')
    i=integer(raw['initial'],0,len(P['initial'])-1,'initial index')
    t=integer(raw['target'],0,len(P['targets'])-1,'target index')
    args=[rational(a) for a in array(raw['parameters'],8,'parameter values',P['r'])]
    loc,initial=P['initial'][i]
    A=Arithmetic(operation_limit)
    state=[A.evaluate(p,args) for p in initial]
    for s in array(raw['steps'],2048,'trace'):
        keys(s,{'edge','inputs'},'trace step')
        j=integer(s['edge'],0,len(P['edges'])-1,'edge index')
        src,dst,u,F=P['edges'][j]
        if src!=loc:
            raise Rejected('trace does not follow control flow')
        us=[rational(a) for a in array(s['inputs'],8,'input values',u)]
        state=[A.evaluate(f,state+us) for f in F]
        loc=dst
    target_loc,p=P['targets'][t]
    if target_loc!=loc:
        raise Rejected('trace ends at wrong observation location')
    value=A.evaluate(p,state)
    if value==0:
        raise Rejected('purported counterexample satisfies the target')
    return {'accepted':True,'kind':'counterexample','value':[str(value.numerator),str(value.denominator)],
            'length':len(raw['steps']),'arithmetic_operations':A.operations}


def no_duplicates(items: list[tuple[str,Any]]) -> dict:
    out={}
    for k,v in items:
        if k in out:
            raise Rejected('duplicate JSON object key')
        out[k]=v
    return out


def read_json(path: str | Path) -> Any:
    data=Path(path).read_bytes()
    if len(data)>MAX_BYTES:
        raise Rejected('file byte limit')
    def reject_float(s: str):
        raise Rejected('floating point / nonfinite JSON not accepted')
    return json.loads(data,object_pairs_hook=no_duplicates,parse_float=reject_float,parse_constant=reject_float)


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('problem')
    parser.add_argument('evidence')
    args=parser.parse_args()
    try:
        p,c=read_json(args.problem),read_json(args.evidence)
        if type(c) is dict and c.get('schema')=='forge-counterexample-v1':
            answer=check_counterexample(p,c)
        else:
            answer=check_certificate(p,c)
        print(json.dumps(answer,sort_keys=True))
        return 0
    except (Rejected,ValueError,TypeError,KeyError,RecursionError,OverflowError) as e:
        print(json.dumps({'accepted':False,'reason':str(e)}))
        return 1

if __name__=='__main__':
    raise SystemExit(main())
