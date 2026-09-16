#!/usr/bin/env python3
"""Deterministic experiments. Run from prototype/; outputs never overwrite recorded results.
The normal default is ../reproduced-results. Authoring run used explicit ../results.
"""
from __future__ import annotations
import argparse, csv, itertools, json, platform, random, sys, time
from pathlib import Path
from fractions import Fraction as F
from ncforge.algebra import *
from ncforge.search import *
from ncforge.checker import verify

SEED=2026091503

def comm(a,b): return add(mul(a,b),mul(b,a),-1)

def anticom(a,b): return add(mul(a,b),mul(b,a))

def sparse_random(rng,m,D,count=6):
    p={}
    for _ in range(count):
        w=tuple(rng.randrange(m) for _ in range(rng.randint(1,D)))
        p=add(p,{w:F(rng.choice([-3,-2,-1,1,2,3]),rng.randint(1,3))})
    return p

def commuting_oracle(p,m):
    a={}
    for w,c in p.items():
        e=tuple(w.count(i) for i in range(m)); a[e]=a.get(e,F(0))+c
    return all(c==0 for c in a.values())

def monomial_oracle(p,generators):
    return all(any(any(w[i:i+len(g)]==g for i in range(len(w)-len(g)+1))
                   for g in generators) for w in p)

def exterior_oracle(p):
    a={}
    for w,c in p.items():
        if len(set(w))!=len(w): continue
        inversions=sum(w[i]>w[j] for i in range(len(w)) for j in range(i+1,len(w)))
        key=tuple(sorted(w)); a[key]=a.get(key,F(0))+(-1)**inversions*c
    return all(c==0 for c in a.values())

def determinant(A):
    """Independent dense Gaussian determinant, used only by principal-minor oracle."""
    A=[[F(x) for x in r] for r in A]; n=len(A); det=F(1)
    for j in range(n):
        k=next((k for k in range(j,n) if A[k][j]),None)
        if k is None: return F(0)
        if k!=j: A[k],A[j]=A[j],A[k]; det=-det
        p=A[j][j]; det*=p
        for i in range(j+1,n):
            a=A[i][j]/p
            for k in range(j+1,n): A[i][k]-=a*A[j][k]
    return det

def principal_psd(A):
    n=len(A)
    return all(determinant([[A[i][j] for j in s] for i in s])>=0
               for k in range(1,n+1) for s in itertools.combinations(range(n),k))

def gram_poly(Q,m,d):
    ws=words(m,d,exact=True); p={}; inv=tuple(range(m))
    for i,u in enumerate(ws):
        for j,v in enumerate(ws):
            p=add(p,{tuple(inv[t] for t in reversed(u))+v:F(Q[i][j])})
    return p

def examples():
    """Returns (label, external problem, produced certificate, production metadata)."""
    out=[]; x,y=var(0),var(1)
    p=power(add(x,y),2); rs=[power(x,2),power(y,2),anticom(x,y)]
    c=equality_search(p,rs,2,2); out.append(('square_zero_sum',problem(p,rs,2),c['certificate'],c['stats']))
    # UA=1 and BV=1 imply U-V=U(B-A)V. Symbol indices U,A,B,V.
    U,A,B,V=[var(i) for i in range(4)]
    rs=[add(mul(U,A),one(),-1),add(mul(B,V),one(),-1)]
    p=add(add(U,V,-1),mul(mul(U,add(B,A,-1)),V),-1)
    c=equality_search(p,rs,4,3); out.append(('resolvent_identity',problem(p,rs,4),c['certificate'],c['stats']))
    # U(1-AB)=1, (1-BA)V=1; coefficient degree 5 is necessary here.
    rs=[add(mul(U,add(one(),mul(A,B),-1)),one(),-1),
        add(mul(add(one(),mul(B,A),-1),V),one(),-1)]
    p=add(mul(U,A),mul(A,V),-1)
    c=equality_search(p,rs,4,5)
    lower=[equality_search(p,rs,4,D)['status'] for D in (2,3,4)]
    meta=dict(c['stats']); meta['bounds_2_3_4']=lower
    out.append(('push_through',problem(p,rs,4),c['certificate'],meta))
    # A self-adjoint idempotent is positive, but x is not a free SOS itself.
    rs=[add(power(x,2),x,-1)]
    c=dictionary_sos(x,rs,[],[x],2,2)
    out.append(('projection_is_positive',problem(x,rs,2,'operator'),c,{'supplied_rays':1}))
    p=mul(mul(y,x),y)
    c=dictionary_sos(p,[],[x],[y],2,3)
    out.append(('positive_congruence',problem(p,[],2,'operator',[x]),c,{'supplied_rays':1}))
    # A homogeneous degree-six square synthesized without a supplied q dictionary.
    q=add(add(mul(power(x,2),y),mul(y,power(x,2)),2),power(y,3),-3)
    p=mul(star(q,(0,1)),q)
    c=homogeneous_sos(p,2)
    out.append(('degree_six_automatic_gram',problem(p,[],2,'operator'),c,{'gram_dimension':8}))
    # Trace positivity must not be promoted to operator positivity.
    h=comm(x,comm(x,y)); p=add(one(),h,2)
    c=dictionary_sos(p,[],[],[one()],2,3,kind='trace')
    out.append(('trace_not_operator',problem(p,[],2,'trace'),c,{'supplied_rays':1}))
    # CHSH squared bound, with a structurally supplied three-ray dictionary.
    A,D,B,C=[var(i) for i in range(4)]
    rs=[add(power(t,2),one(),-1) for t in (A,D,B,C)]
    rs += [comm(s,t) for s in (A,D) for t in (B,C)]
    S=add(mul(A,add(B,C)),mul(D,add(B,C,-1)))
    p=add(scale(one(),8),mul(star(S,(0,1,2,3)),S),-1)
    qs=involution_dictionary(rs,4)
    c=dictionary_sos(p,rs,[],qs,4,4,max_support=3)
    if c is None: raise AssertionError('CHSH structural-dictionary reconstruction failed')
    out.append(('chsh_squared_bound',problem(p,rs,4,'operator'),c,
                {'generated_rays':len(qs),'bound':4,'automatic_dictionary_discovery':'involution_commutation_graph','target':'8 - adjoint(S) S'}))
    symmetry=add(S,star(S,(0,1,2,3)),-1)
    sc=equality_search(symmetry,rs,4,2)
    out.append(('chsh_self_adjointness',problem(symmetry,rs,4),sc['certificate'],sc['stats']))
    return out

def run(destination):
    destination.mkdir(parents=True,exist_ok=True)
    rng=random.Random(SEED); records=[]; summaries=[]; negative_gram=[]
    def store(name,family,prob,cert,meta=None):
        check=verify(prob,cert)
        if not check['accepted']: raise AssertionError((name,check))
        records.append({'name':name,'family':family,'problem':prob,'certificate':cert,
                        'replay':check,'producer_metadata':meta or {}})
    # Each family has 30 independently labelled queries, not 30 selected successes.
    for family,m in [('commuting',2),('monomial',2),('exterior',3)]:
        xs=[var(i) for i in range(m)]; D=3
        if family=='commuting':
            rs=[comm(xs[0],xs[1])]; oracle=lambda p:commuting_oracle(p,m)
        elif family=='monomial':
            gs=[(0,0),(1,0,1)]; rs=[{g:F(1)} for g in gs]; oracle=lambda p:monomial_oracle(p,gs)
        else:
            rs=[power(x,2) for x in xs]+[anticom(xs[i],xs[j]) for i in range(m) for j in range(i)]
            oracle=exterior_oracle
        cols,_=contexts(rs,m,D); positive=negative=0; dims=[]; start=time.perf_counter()
        for i in range(30):
            if i%2==0:
                p={}
                for _ in range(4): p=add(p,rng.choice(cols),F(rng.choice([-2,-1,1,2])))
            else: p=sparse_random(rng,m,D)
            expected=oracle(p); ans=equality_search(p,rs,m,D)
            assert (ans['status']=='certificate')==expected,(family,i,'oracle disagreement')
            if expected:
                positive+=1; cert=ans['certificate']
            else:
                negative+=1; cert=quotient_countermodel(p,rs,m)
                assert cert is not None; dims.append(cert['dimension'])
            store(f'{family}_{i:02d}',family,problem(p,rs,m),cert,
                  {'oracle_member':expected,**ans['stats']})
        summaries.append({'family':family,'queries':30,'positive_certificates':positive,
                          'matrix_countermodels':negative,'oracle_disagreements':0,
                          'max_countermodel_dimension':max(dims,default=0),
                          'seconds':time.perf_counter()-start})
    # Unique Gram matrix versus an independently computed principal-minor predicate.
    positive=negative=0; start=time.perf_counter()
    for i in range(40):
        n=4
        if i<20:
            A=[[F(rng.randint(-3,3)) for _ in range(n)] for _ in range(3)]
            Q=[[sum((r[j]*r[k] for r in A),F(0)) for k in range(n)] for j in range(n)]
        else:
            Q=[[F(0) for _ in range(n)] for _ in range(n)]
            for j in range(n):
                for k in range(j,n):
                    Q[j][k]=Q[k][j]=F(rng.randint(-3,3)) if j!=k else F(rng.randint(0,3))
        expected=principal_psd(Q); p=gram_poly(Q,2,2); cert=homogeneous_sos(p,2)
        assert (cert is not None)==expected,('Gram oracle disagreement',i)
        if cert is not None:
            positive+=1; store(f'gram_{i:02d}','homogeneous_gram',problem(p,[],2,'operator'),cert,
                              {'gram':[[rational(x) for x in row] for row in Q],
                               'principal_minor_oracle':True})
        else:
            negative+=1
            negative_gram.append({'name':f'gram_{i:02d}','problem':problem(p,[],2,'operator'),
                                  'gram':[[rational(x) for x in row] for row in Q],
                                  'principal_minor_oracle':False,'producer_result':'no_certificate'})
    summaries.append({'family':'homogeneous_gram','queries':40,'positive_certificates':positive,
                      'outside_homogeneous_square_cone':negative,'oracle_disagreements':0,
                      'seconds':time.perf_counter()-start})
    # Hand-specified goals test automatic solving, not automatic source extraction.
    start=time.perf_counter(); ex=examples()
    for name,p,c,meta in ex: store(name,'worked_examples',p,c,meta)
    summaries.append({'family':'worked_examples','queries':len(ex),'positive_certificates':len(ex),
                      'seconds':time.perf_counter()-start})
    # Same query and producer, with / without exact incidence-component slicing.
    ablation=[]
    for m in (3,4,5,6):
        xs=[var(i) for i in range(m)]
        rs=[comm(xs[i],xs[j]) for i in range(m) for j in range(i)]
        p=comm(power(xs[0],3),xs[1]); row={'atoms':m,'bound':4}
        for sliced in (False,True):
            start=time.perf_counter(); ans=equality_search(p,rs,m,4,slice_support=sliced)
            secs=time.perf_counter()-start; assert ans['status']=='certificate'
            check=verify(problem(p,rs,m),ans['certificate']); assert check['accepted']
            tag='sliced' if sliced else 'full'
            row.update({tag+'_seconds':secs,tag+'_rank':ans['stats']['rank'],
                        tag+'_selected':ans['stats']['columns_selected'],
                        tag+'_certificate_terms':len(ans['certificate']['ideal'])})
        row['columns_assembled']=ans['stats']['columns_total']; ablation.append(row)
    result={'seed':SEED,'python':sys.version,'platform':platform.platform(),
            'dependency_policy':'Python standard library; authoring command used python -S',
            'lean_status':'NOT_RUN: no Lean executable available',
            'families':summaries,'ablation':ablation,'stored_evidence_objects':len(records)}
    (destination/'certificates.json').write_text(json.dumps(records,indent=2)+'\n')
    (destination/'negative-gram-queries.json').write_text(json.dumps(negative_gram,indent=2)+'\n')
    (destination/'experiments.json').write_text(json.dumps(result,indent=2)+'\n')
    with (destination/'slicing.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(ablation[0]));w.writeheader();w.writerows(ablation)
    print(json.dumps(result,indent=2))
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path,default=Path('../reproduced-results'))
    run(ap.parse_args().output)
