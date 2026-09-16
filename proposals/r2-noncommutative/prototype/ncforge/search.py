"""Untrusted exact producers. All emitted evidence must pass checker.py."""
from __future__ import annotations
from collections import defaultdict, deque
from fractions import Fraction as F
from itertools import combinations
from .algebra import *

class BudgetExceeded(Exception): pass

def contexts(relations:list[Poly],m:int,D:int,max_columns=20000):
    if type(D) is not int or D<0: raise ValueError('nonnegative bound required')
    columns=[]; labels=[]
    for j,r in enumerate(relations):
        if not r: continue
        for ell in range(D-degree(r)+1):
            for w in words(m,ell,exact=True):
                for cut in range(ell+1):
                    if len(columns)>=max_columns: raise BudgetExceeded('context column cap')
                    u,v=w[:cut],w[cut:]
                    columns.append(sandwich(r,u,v)); labels.append((j,u,v))
    return columns,labels

def relevant_columns(p:Poly,columns:list[Poly])->list[int]:
    """Exact incidence-component slice; full column assembly precedes slicing."""
    incident=defaultdict(list)
    for i,col in enumerate(columns):
        for w in col: incident[w].append(i)
    seen_words=set(p); seen_cols=set(); todo=deque(p)
    while todo:
        for i in incident[todo.popleft()]:
            if i in seen_cols: continue
            seen_cols.add(i)
            for w in columns[i]:
                if w not in seen_words: seen_words.add(w); todo.append(w)
    return sorted(seen_cols)

def ideal_items(coeff:dict[int,F],labels:list)->list[dict]:
    return [{'relation':labels[i][0],'left':list(labels[i][1]),'right':list(labels[i][2]),
             'weight':rational(c)} for i,c in sorted(coeff.items()) if c]

def equality_search(p:Poly,relations:list[Poly],m:int,D:int,*,slice_support=True,
                    max_columns=20000)->dict:
    columns,labels=contexts(relations,m,D,max_columns)
    selected=relevant_columns(p,columns) if slice_support else list(range(len(columns)))
    basis=Echelon()
    for i in selected: basis.insert(columns[i],i)
    coeff=basis.solve(p)
    stats={'bound':D,'columns_total':len(columns),'columns_selected':len(selected),'rank':len(basis.rows)}
    if coeff is not None:
        return {'status':'certificate','certificate':{'schema':'ncforge.certificate.v1',
                'kind':'equality','ideal':ideal_items(coeff,labels)},'stats':stats}
    # A template obstruction is NOT a counterexample to the original proposition.
    return {'status':'unknown','reason':'outside_bounded_context_span','stats':stats}

def quotient_countermodel(p:Poly,relations:list[Poly],m:int,*,max_dimension=100)->dict | None:
    """Finite left-regular model of the degree-D truncation. Homogeneous relations ONLY."""
    if not all(homogeneous(r) for r in relations): return None
    D=degree(p)
    if sum(m**k for k in range(D+1))>4000: raise BudgetExceeded('quotient ambient cap')
    cols,_=contexts(relations,m,D)
    basis=Echelon()
    for i,col in enumerate(cols): basis.insert(col,i)
    if basis.solve(p) is not None: return None
    allwords=words(m,D)
    free=[w for w in allwords if w not in basis.rows]
    if len(free)>max_dimension: raise BudgetExceeded('matrix dimension cap')
    ix={w:i for i,w in enumerate(free)}; n=len(free)
    def normal(w):
        if len(w)>D: return {}
        return basis.reduce({w:F(1)})[0]
    matrices=[]
    for a in range(m):
        M=[[F(0) for _ in range(n)] for _ in range(n)]
        for j,w in enumerate(free):
            for v,c in normal((a,)+w).items(): M[ix[v]][j]+=c
        matrices.append([[rational(x) for x in row] for row in M])
    v=[F(0)]*n
    for w,c in normal(()).items(): v[ix[w]]=c
    return {'schema':'ncforge.certificate.v1','kind':'matrix_countermodel','dimension':n,
            'matrices':matrices,'vector':[rational(x) for x in v]}

def homogeneous_sos(p:Poly,m:int,involution:tuple[int,...]|None=None)->dict | None:
    inv=tuple(range(m)) if involution is None else involution
    if not p: return {'schema':'ncforge.certificate.v1','kind':'operator','squares':[],'ideal':[]}
    if not homogeneous(p) or degree(p)%2 or star(p,inv)!=p: return None
    d=degree(p)//2; ws=words(m,d,exact=True); ix={w:i for i,w in enumerate(ws)}
    Q=[[F(0) for _ in ws] for _ in ws]
    for w,c in p.items():
        u=tuple(inv[i] for i in reversed(w[:d])); v=w[d:]
        Q[ix[u]][ix[v]]+=c
    dec=ldl_squares(Q)
    if dec is None: return None
    return {'schema':'ncforge.certificate.v1','kind':'operator','ideal':[],
            'squares':[{'weight':rational(d),'positive':-1,
                       'q':encode({w:c for w,c in zip(ws,row) if c})} for d,row in dec]}

def commutator_receipt(p:Poly)->list[dict]:
    if cyclic(p): raise ValueError('residual does not have zero cyclic normal form')
    out=[]
    for w,c in sorted(p.items()):
        canon=cyclic_word(w)
        if w==canon: continue
        k=next(k for k in range(1,len(w)) if w[k:]+w[:k]==canon)
        out.append({'weight':rational(c),'left':list(w[:k]),'right':list(w[k:])})
    return out

def dictionary_sos(p:Poly,relations:list[Poly],positives:list[Poly],qs:list[Poly],m:int,D:int,
                   *,kind='operator',max_support=4,max_attempts=10000)->dict | None:
    """Exact finite-ray search after quotienting equalities; trace supports no relations here.
    Exhaustive within the enumerated supports, not a general SDP/positivity decision procedure.
    """
    if kind not in ('operator','trace'): raise ValueError('bad kind')
    inv=tuple(range(m))
    if star(p,inv)!=p or any(star(g,inv)!=g for g in positives): return None
    if kind=='trace' and relations: raise ValueError('trace relation search not implemented')
    cols,labels=contexts(relations,m,D); ib=Echelon()
    for i,col in enumerate(cols): ib.insert(col,i)
    def project(q):
        return cyclic(q) if kind=='trace' else ib.reduce(q)[0]
    rays=[]; descriptors=[]
    for gi,g in enumerate([one()]+positives):
        for q in qs:
            rays.append(mul(mul(star(q,inv),g),q)); descriptors.append((gi-1,q))
    target=project(p); reduced=[project(q) for q in rays]
    attempts=0
    supports=[()] if not target else []
    for k in range(1,min(max_support,len(rays))+1):
        for support in combinations(range(len(rays)),k):
            attempts+=1
            if attempts>max_attempts: return None
            eb=Echelon()
            for j in support: eb.insert(reduced[j],j)
            coeff=eb.solve(target)
            if coeff is not None and all(c>=0 for c in coeff.values()):
                supports=[tuple(coeff.items())]; break
        if supports: break
    if not supports: return None
    coeff=dict(supports[0]); residual=p.copy(); squares=[]
    for j,c in sorted(coeff.items()):
        if not c: continue
        residual=add(residual,rays[j],-c); gi,q=descriptors[j]
        squares.append({'weight':rational(c),'positive':gi,'q':encode(q)})
    cert={'schema':'ncforge.certificate.v1','kind':kind,'squares':squares,'ideal':[]}
    if kind=='trace': cert['commutators']=commutator_receipt(residual)
    else:
        ic=ib.solve(residual)
        if ic is None: raise AssertionError('producer internal reconstruction error')
        cert['ideal']=ideal_items(ic,labels)
    return cert

def involution_dictionary(relations:list[Poly],m:int,*,max_pairs=20)->list[Poly]:
    """Untrusted structural ray proposal for self-adjoint involutive generators.
    Recognizes scaled x_i^2-1 and scaled x_i*x_j-x_j*x_i literally.
    Noncommuting pairs propose commutators/anticommutators; two cross-commuting
    pairs also propose the sum and difference of their commutators.
    Missing a pattern loses search power only; every eventual identity is replayed.
    """
    invol=set(); commuting=set()
    for r in relations:
        if len(r)!=2: continue
        for w,c in r.items():
            if len(w)==2 and w[0]==w[1] and r.get(())==-c: invol.add(w[0])
            if len(w)==2 and w[0]!=w[1] and r.get(w[::-1])==-c:
                commuting.add(frozenset(w))
    pairs=[(i,j) for i in sorted(invol) for j in sorted(invol)
           if i<j and frozenset((i,j)) not in commuting]
    if len(pairs)>max_pairs: raise BudgetExceeded('involution-pair dictionary cap')
    rays=[]; comms=[]
    for i,j in pairs:
        a={(i,j):F(1),(j,i):F(1)};c={(i,j):F(1),(j,i):F(-1)}
        rays.extend((a,c));comms.append(c)
    for i in range(len(pairs)):
        for j in range(i):
            if set(pairs[i]).isdisjoint(pairs[j]) and all(
                    frozenset((a,b)) in commuting for a in pairs[i] for b in pairs[j]):
                rays.extend((add(comms[i],comms[j]),add(comms[i],comms[j],-1)))
    # Canonical duplicates removed, with q and -q identified only here in search.
    out=[];seen=set()
    for q in rays:
        if not q: continue
        first=q[min(q)];q=scale(q,1/first)
        key=tuple(sorted(q.items()))
        if key not in seen: seen.add(key);out.append(q)
    return out
