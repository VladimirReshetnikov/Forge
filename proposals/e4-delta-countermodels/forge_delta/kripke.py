"""Finite Kripke countermodel replay and an intentionally small model proposer.

Accepts NONDERIVABILITY IN THE OBJECT LOGIC IPC, not the negation of a Lean
proposition, and not absence of an inhabitant in arbitrary Lean environments.
The checker and proposer use different forcing implementations.
"""
from __future__ import annotations
from itertools import product
from functools import lru_cache
from time import perf_counter
from typing import Any
from .checker import Invalid, require, integer, keys


def atom(name):return ['var',name]
def bot():return ['bot']
def imp(a,b):return ['imp',a,b]
def conj(a,b):return ['and',a,b]
def disj(a,b):return ['or',a,b]
def neg(a):return imp(a,bot())


def formula(raw: Any, depth: int=0, fuel: list|None=None) -> tuple:
    if fuel is None:fuel=[0]
    fuel[0]+=1
    require(depth<=64 and fuel[0]<=1024,'formula budget')
    require(type(raw) is list and len(raw)>=1 and type(raw[0]) is str,'formula node')
    tag=raw[0]
    if tag=='var':
        require(len(raw)==2 and type(raw[1]) is str and 0<len(raw[1])<=128,'atom')
        return (tag,raw[1])
    if tag=='bot':
        require(len(raw)==1,'bottom arity');return (tag,)
    require(tag in {'and','or','imp'} and len(raw)==3,'connective/arity')
    return (tag,formula(raw[1],depth+1,fuel),formula(raw[2],depth+1,fuel))


def atoms(f:tuple)->set[str]:
    if f[0]=='var':return {f[1]}
    if f[0]=='bot':return set()
    return atoms(f[1])|atoms(f[2])


def parse_problem(p):
    keys(p,{'version','kind','logic','context','goal'})
    require(type(p['version']) is int and p['version']==1 and p['kind']=='propositional_sequent'
            and p['logic']=='IPC','unsupported logic')
    require(type(p['context']) is list and len(p['context'])<=64,'context budget')
    ctx=[formula(f) for f in p['context']];g=formula(p['goal'])
    names=set().union(*(atoms(f) for f in ctx+[g]))
    require(len(names)<=16,'atom budget')
    return ctx,g,sorted(names)


def sequent(goal,context=None):
    return {'version':1,'kind':'propositional_sequent','logic':'IPC',
            'context':[] if context is None else context,'goal':goal}


def _check(p,c):
    ctx,g,names=parse_problem(p)
    keys(c,{'kind','worlds','root','relation','valuation'})
    require(c['kind']=='finite_kripke_countermodel','countermodel kind')
    n=integer(c['worlds'],1,32);root=integer(c['root'],0,n-1)
    r=c['relation'];val=c['valuation']
    require(type(r) is list and len(r)==n,'relation rows')
    for row in r:require(type(row) is list and len(row)==n and all(type(v) is bool for v in row),'relation values')
    require(all(r[i][i] for i in range(n)),'nonreflexive relation')
    require(all(r[root][i] for i in range(n)),'root not least')
    for i in range(n):
        for j in range(n):
            require(i==j or not(r[i][j] and r[j][i]),'not antisymmetric')
            for k in range(n):require(not(r[i][j] and r[j][k]) or r[i][k],'not transitive')
    require(type(val) is dict and set(val)==set(names),'valuation atom coverage')
    for name,vs in val.items():
        require(type(vs) is list and len(vs)==n and all(type(v) is bool for v in vs),'valuation values')
        for i in range(n):
            for j in range(n):require(not(vs[i] and r[i][j]) or vs[j],'nonmonotone valuation')
    # Recursive semantics, as in the mathematical definition. Do NOT trust a
    # truth table, witness annotations, or the proposer's bitset evaluation.
    @lru_cache(None)
    def force(w,f):
        if f[0]=='var':return val[f[1]][w]
        if f[0]=='bot':return False
        if f[0]=='and':return force(w,f[1]) and force(w,f[2])
        if f[0]=='or':return force(w,f[1]) or force(w,f[2])
        return all(not r[w][v] or not force(v,f[1]) or force(v,f[2]) for v in range(n))
    require(all(force(root,f) for f in ctx),'context false at root')
    require(not force(root,g),'goal true at root')


def verify_countermodel(problem,cert)->bool:
    try:
        _check(problem,cert);return True
    except (Invalid,TypeError,ValueError,KeyError,IndexError,RecursionError):return False


def tree_frames(n):
    """Rooted trees in parent-before-child order, including duplicate isomorphs.

    Does not enumerate all finite partial orders. Finite rooted-tree
    unravelings suffice semantically for IPC, but a world cap is incomplete.
    """
    for parents in product(*(range(i) for i in range(1,n))):
        succ=[1<<i for i in range(n)]
        for i in range(n-1,0,-1):succ[parents[i-1]]|=succ[i]
        yield succ


def truth_bits(f,valuation,succ,allbits,cache):
    if f in cache:return cache[f]
    if f[0]=='var':b=valuation[f[1]]
    elif f[0]=='bot':b=0
    else:
        a=truth_bits(f[1],valuation,succ,allbits,cache)
        c=truth_bits(f[2],valuation,succ,allbits,cache)
        if f[0]=='and':b=a&c
        elif f[0]=='or':b=a|c
        else:
            bad=a & (allbits^c)
            b=sum(1<<w for w,s in enumerate(succ) if not(s&bad))
    cache[f]=b;return b


def find_countermodel(problem,max_worlds=3,max_models=200000):
    ctx,g,names=parse_problem(problem)
    if not(1<=max_worlds<=6):raise ValueError('max_worlds must be 1..6')
    t=perf_counter();models=0;frames=0
    for n in range(1,max_worlds+1):
        full=(1<<n)-1
        for succ in tree_frames(n):
            frames+=1
            upward=[b for b in range(1<<n) if all(not(b>>w&1) or b&s==s for w,s in enumerate(succ))]
            for vals in product(upward,repeat=len(names)):
                if models>=max_models:
                    return {'status':'unknown','reason':'model budget',
                            'stats':{'models':models,'frames':frames,'elapsed_seconds':perf_counter()-t}}
                models+=1;v=dict(zip(names,vals,strict=True));cache={}
                if all(truth_bits(f,v,succ,full,cache)&1 for f in ctx) and not(truth_bits(g,v,succ,full,cache)&1):
                    cert={'kind':'finite_kripke_countermodel','worlds':n,'root':0,
                          'relation':[[bool(s>>j&1) for j in range(n)] for s in succ],
                          'valuation':{name:[bool(b>>j&1) for j in range(n)] for name,b in v.items()}}
                    if not verify_countermodel(problem,cert):raise AssertionError('Kripke replay failed')
                    return {'status':'ipc_countermodel','certificate':cert,
                            'stats':{'models':models,'frames':frames,'elapsed_seconds':perf_counter()-t}}
    return {'status':'unknown','reason':'world bound exhausted; no validity claim',
            'stats':{'models':models,'frames':frames,'elapsed_seconds':perf_counter()-t}}
