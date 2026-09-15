"""Ranking synthesis for supplied cyclic obligation graphs; SCT diagnostics.

NOT a Lean proof search engine. A ranking certifies only descent of the supplied
calls. Local proof constructors, all branches, and call-argument translations
still have to be proved before a cyclic search graph can become a theorem.
"""
from __future__ import annotations
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations,product,permutations
from exact import coordinates,encode_q


def as_q(x):
    return tuple(map(Q,x))


def sub(a,b):
    return tuple(x-y for x,y in zip(a,b))


def substitute(a,fs):
    z=[a[0]]+[Q(0)]*(len(a)-1)
    for c,f in zip(a[1:],fs):
        z=[x+c*y for x,y in zip(z,f)]
    return tuple(z)


def all_guards(edge,n):
    return tuple([as_q(g) for g in edge['guards']] +
                 [tuple(Q(j==i+1) for j in range(n+1)) for i in range(n)] +
                 [tuple(Q(j==0) for j in range(n+1))])


@lru_cache(maxsize=20000)
def cone(target,guards):
    """Exact low-dimensional conic membership by independent supports.

    Conic Caratheodory bounds the necessary support by the ambient dimension.
    Enumeration is exponential in dimension, appropriate only for this prototype.
    """
    if not any(target):
        return tuple(Q(0) for _ in guards)
    for k in range(1,min(len(target),len(guards))+1):
        for idx in combinations(range(len(guards)),k):
            cs=coordinates([guards[i] for i in idx],list(target))
            if cs is not None and all(c>=0 for c in cs):
                out=[Q(0)]*len(guards)
                for i,c in zip(idx,cs):
                    out[i]=c
                return tuple(out)
    return None


def try_layers(problem,layers):
    n=problem['n']
    witnesses=[]
    for edge in problem['edges']:
        fs=[as_q(f) for f in edge['updates']]
        gs=all_guards(edge,n)
        dom=[cone(f,gs) for f in fs]
        if any(d is None for d in dom):
            return None
        for pivot,layer in enumerate(layers):
            diff=sub(as_q(layer[edge['source']]),
                     substitute(as_q(layer[edge['target']]),fs))
            strict=(diff[0]-1,)+diff[1:]
            cs=cone(strict,gs)
            if cs is not None:
                witnesses.append(dict(pivot=pivot,
                    decrease=[encode_q(c) for c in cs],
                    target_nonnegative=[[encode_q(c) for c in d] for d in dom]))
                break
            if any(diff):
                return None  # prior lexicographic coordinates must be equal
        else:
            return None
    return dict(kind='ranking-v1',layers=layers,edges=witnesses)


def synthesize(problem,weight_bound=3,phase_bound=2):
    n=problem['n']; nodes=problem['nodes']; attempts=0
    weights=[w for w in product(range(weight_bound+1),repeat=n) if any(w)]
    weights.sort(key=lambda w:(sum(w),w))
    phases=[p for p in product(range(phase_bound+1),repeat=len(nodes)) if min(p)==0]
    phases.sort(key=lambda p:(sum(p),p))
    for w in weights:
        for ps in phases:
            layers=[{q:[p,*w] for q,p in zip(nodes,ps)}]
            attempts+=1
            c=try_layers(problem,layers)
            if c:
                return c,dict(attempts=attempts,mode='affine',status='found')
    # A bounded second grammar: permutations of the original natural measures.
    for order in permutations(range(n)):
        layers=[{q:[0]+[int(j==i) for j in range(n)] for q in nodes} for i in order]
        attempts+=1
        c=try_layers(problem,layers)
        if c:
            return c,dict(attempts=attempts,mode='lexicographic',status='found')
    return None,dict(attempts=attempts,mode=None,status='unknown',
                     reason='bounded ranking grammars exhausted')


# 0 = no known comparison; 1 = non-increase; 2 = strict decrease.
def compose(g,h,n):
    return tuple(max((0 if not g[i*n+k] or not h[k*n+j]
                      else max(g[i*n+k],h[k*n+j]) for k in range(n)),default=0)
                 for i in range(n) for j in range(n))


def size_change(problem):
    n=problem['n']; known=set()
    for e in problem['edges']:
        gs=all_guards(e,n); fs=[as_q(f) for f in e['updates']]; vals=[]
        for i in range(n):
            x=tuple(Q(j==i+1) for j in range(n+1))
            for f in fs:
                d=sub(x,f)
                if cone((d[0]-1,)+d[1:],gs) is not None:
                    vals.append(2)
                elif cone(d,gs) is not None:
                    vals.append(1)
                else:
                    vals.append(0)
        known.add((e['source'],e['target'],tuple(vals)))
    todo=list(known)
    while todo:
        a,b,g=todo.pop()
        for c,d,h in tuple(known):
            candidates=[]
            if b==c:
                candidates.append((a,d,compose(g,h,n)))
            if d==a:
                candidates.append((c,b,compose(h,g,n)))
            for item in candidates:
                if item not in known:
                    known.add(item); todo.append(item)
    bad=[]
    for a,b,g in known:
        if a==b and compose(g,g,n)==g and not any(g[i*n+i]==2 for i in range(n)):
            bad.append(dict(node=a,matrix=list(g)))
    return dict(criterion_met=not bad,closure_size=len(known),
                bad_idempotents=sorted(bad,key=lambda x:(x['node'],x['matrix'])))


def fixtures():
    def graph(name,n,nodes,edges):
        return dict(name=name,n=n,nodes=nodes,edges=[
            dict(source=a,target=b,guards=g,updates=f) for a,b,g,f in edges])
    return [
        graph('two_phase',1,['P','Q'],[
            ('P','Q',[],[[0,1]]),('Q','P',[[-1,1]],[[-1,1]])]),
        graph('swapped_arguments',2,['P'],[
            ('P','P',[[-1,1,0]],[[0,0,1],[-1,1,0]])]),
        graph('subtractive_euclid',2,['P'],[
            ('P','P',[[-1,1,-1],[-1,0,1]],[[0,1,-1],[0,0,1]]),
            ('P','P',[[-1,-1,1],[-1,1,0]],[[0,1,0],[0,-1,1]])]),
        graph('lexicographic_growth',2,['P'],[
            ('P','P',[[-1,1,0]],[[-1,1,0],[0,0,2]]),
            ('P','P',[[-1,0,1]],[[0,1,0],[-1,0,1]])]),
        graph('invalid_identity_cycle',1,['P'],[('P','P',[],[[0,1]])]),
        graph('invalid_alternating_decrease',2,['P'],[
            ('P','P',[[-1,1,0]],[[-1,1,0],[1,0,1]]),
            ('P','P',[[-1,0,1]],[[1,1,0],[-1,0,1]])]),
    ]
