"""Target-seeded pullback ideal completion, with exact membership witnesses.

Unconditional polynomial transitions over Q only. A small traced Buchberger
implementation proposes polynomial multipliers; independent replay never runs
Buchberger. Resource bounds yield UNKNOWN. This is not general guarded-program
invariant generation and does not compute the strongest invariant ideal.
"""
from __future__ import annotations
from itertools import combinations,product
from exact import Q,const,var,add,scale,mul,power,subst,encode
from invariant_space import Problem

class Budget(Exception): pass


def leading(p): return max(p,key=lambda e:(sum(e),e))

def divides(a,b): return all(x<=y for x,y in zip(a,b))

def quotient_term(a,ac,b,bc):
    return {tuple(x-y for x,y in zip(a,b)):ac/bc}


def divide(p,gs,n):
    qs=[{} for _ in gs]; r={};p=dict(p);steps=0
    while p:
        steps+=1
        if steps>20000 or len(p)>5000: raise Budget('division work bound')
        a=leading(p);ac=p[a]
        for i,g in enumerate(gs):
            if not g:continue
            b=leading(g)
            if divides(b,a):
                t=quotient_term(a,ac,b,g[b]);qs[i]=add(qs[i],t)
                p=add(p,scale(-1,mul(t,g)))
                break
        else:
            r=add(r,{a:ac});del p[a]
    return qs,r


def combine(cs,rs,n):
    out=[{} for _ in range(n)]
    for c,r in zip(cs,rs):
        for j,v in enumerate(r):out[j]=add(out[j],mul(c,v))
    return out


def groebner_traced(gens,n,max_pairs=2000):
    """Each returned basis element has an exact expression in original gens."""
    m=len(gens);gs=[];rs=[]
    for j,g in enumerate(gens):
        if not g:continue
        c=1/g[leading(g)]
        gs.append(scale(c,g));rs.append([const(n,c) if k==j else {} for k in range(m)])
    pending=list(combinations(range(len(gs)),2));count=0
    while pending:
        i,j=pending.pop(0);count+=1
        if count>max_pairs or len(gs)>64:raise Budget('Groebner pair/basis bound')
        a,b=leading(gs[i]),leading(gs[j]);l=tuple(max(x,y) for x,y in zip(a,b))
        u={tuple(x-y for x,y in zip(l,a)):1/gs[i][a]}
        v={tuple(x-y for x,y in zip(l,b)):1/gs[j][b]}
        s=add(mul(u,gs[i]),scale(-1,mul(v,gs[j])))
        repr_s=[add(mul(u,x),scale(-1,mul(v,y))) for x,y in zip(rs[i],rs[j])]
        qs,r=divide(s,gs,n)
        if r:
            sub=combine(qs,rs,m)
            rr=[add(x,scale(-1,y)) for x,y in zip(repr_s,sub)]
            c=1/r[leading(r)];r=scale(c,r);rr=[scale(c,x) for x in rr]
            pending.extend((k,len(gs)) for k in range(len(gs)))
            gs.append(r);rs.append(rr)
    return gs,rs,count


def member(p,gs,rs,n,m):
    qs,r=divide(p,gs,n)
    return (None if r else combine(qs,rs,m))


def separating_point(p,k):
    if not p:return None
    # A nonzero polynomial of degree <=d in each variable is nonzero somewhere
    # on {0,...,d}^k over Q. This is a proof-directed finite grid, not a heuristic.
    d=max((max(e,default=0) for e in p),default=0)
    if (d+1)**k>10000:raise Budget('counterexample grid bound')
    for xs in product(range(d+1),repeat=k):
        if subst(p,[const(0,x) for x in xs],0):return xs
    raise AssertionError('nonzero polynomial disappeared on separating grid')


def complete(problem,max_generators=16,max_degree=24):
    n=problem.n;gens=[problem.target];words=[[]];rounds=0;pairs=0
    try:
        while True:
            for g,word in zip(gens,words):
                initial=subst(g,problem.init,problem.init_parameters)
                if initial:
                    point=separating_point(initial,problem.init_parameters)
                    cert=dict(kind='polynomial-orbit-counterexample-v1',
                              parameters=[[x,1] for x in point],word=word)
                    return cert,dict(status='counterexample',rounds=rounds,generators=len(gens),groebner_pairs=pairs)
            gs,rs,used=groebner_traced(gens,n);pairs+=used
            actions=[];addition=None
            for a,f in enumerate(problem.transitions):
                rows=[]
                for g,word in zip(gens,words):
                    p=subst(g,f,n)
                    if any(sum(e)>max_degree for e in p):raise Budget('pullback degree bound')
                    c=member(p,gs,rs,n,len(gens))
                    if c is None:
                        addition=(p,[a]+word);break
                    rows.append(c)
                if addition is not None:break
                actions.append(rows)
            if addition is None:
                cert=dict(kind='pullback-ideal-v1',generators=[encode(g) for g in gens],
                    actions=[[[encode(h) for h in row] for row in a] for a in actions],
                    target_coefficients=[encode(const(n,1))]+[[] for _ in gens[1:]])
                return cert,dict(status='found',rounds=rounds,generators=len(gens),groebner_pairs=pairs)
            if len(gens)>=max_generators:raise Budget('generator bound')
            gens.append(addition[0]);words.append(addition[1]);rounds+=1
    except Budget as ex:
        return None,dict(status='unknown',reason=str(ex),rounds=rounds,generators=len(gens),groebner_pairs=pairs)


def fixtures():
    x=var(1,0)
    yield Problem('ideal_degree_growth',1,1,0,[const(0,0)],[[mul(x,x)]],x)
    from invariant_space import coupled_example
    p=coupled_example();p.name='ideal_coupled_target';yield p
    x,y=var(2,0),var(2,1);t=var(1,0)
    for i,(p,q,a) in enumerate(product((2,3),(2,3,4),(2,3))):
        yield Problem(f'ideal_power_curve_{i:02}',2,max(p,q),1,[power(t,q,1),power(t,p,1)],
                      [[power(x,a,2),power(y,a,2)]],add(power(x,p,2),scale(-1,power(y,q,2))))
    yield Problem('orbit_counterexample_one_step',1,1,0,[const(0,0)],[[add(x1:=var(1,0),const(1,1))]],x1)
    yield Problem('orbit_counterexample_two_steps',2,1,0,[const(0,0),const(0,0)],[[y,const(2,1)]],x)
    yield Problem('orbit_counterexample_noncommuting',2,1,0,[const(0,0),const(0,0)],
                  [[y,const(2,0)],[const(2,0),const(2,1)]],x)
