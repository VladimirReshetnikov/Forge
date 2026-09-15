"""Proof-producing CDCL(T) for Boolean CNF + integer difference constraints.

Proof rules: original clause; negative balanced cycle; binary resolution.
Theory atom i means value[v]-value[u] <= c, where atoms[i]=(u,v,c).
Its negation means value[u]-value[v] <= -c-1 (INTEGERS ONLY).
The implementation is intentionally small: scanning propagation and
Bellman-Ford, no watched literals, restarts, or production SAT backend.
"""
from __future__ import annotations
from itertools import product


def edge(lit, atoms):
    u,v,c=atoms[abs(lit)]
    return (u,v,c) if lit>0 else (v,u,-c-1)

def difference_check(trail,atoms,nodes):
    edges=[(*edge(l,atoms),l) for l in trail if abs(l) in atoms]
    d=[0]*nodes;pred=[None]*nodes;changed=None
    for _ in range(nodes):
        changed=None
        for u,v,c,l in edges:
            if d[v]>d[u]+c:
                d[v]=d[u]+c;pred[v]=(u,v,c,l);changed=v
        if changed is None:return None,d
    if changed is None:return None,d
    v=changed
    for _ in range(nodes):v=pred[v][0]
    start=v;cycle=[]
    while True:
        e=pred[v];cycle.append(e[3]);v=e[0]
        if v==start:break
        if len(cycle)>nodes:raise AssertionError('cycle extraction')
    return cycle,d

def resolve(c1,c2,pivot):
    if pivot not in c1 or -pivot not in c2:
        raise ValueError('invalid resolution pivot')
    return (c1-{pivot}) | (c2-{-pivot})

def solve(cnf, atoms=None, nodes=1, max_conflicts=100000):
    atoms={} if atoms is None else atoms
    if nodes<1 or any(type(l) is not int or l==0 for c in cnf for l in c):
        raise ValueError('invalid input')
    for k,(u,v,c) in atoms.items():
        if type(k) is not int or k<=0 or not 0<=u<nodes or not 0<=v<nodes or type(c) is not int:
            raise ValueError('invalid theory atom')
    proofs=[];clauses=[]
    def append(clause,kind,**kw):
        clause=frozenset(clause)
        idx=len(proofs)
        proofs.append({'kind':kind,'clause':sorted(clause),**kw})
        clauses.append(clause)
        return idx
    for i,c in enumerate(cnf):append(c,'input',index=i)
    variables=sorted(set(abs(l) for c in cnf for l in c)|set(atoms))
    val={};level={};reason={};trail=[];dl=0
    activity={v:sum(v==abs(l) for c in cnf for l in c) for v in variables}
    stats={'decisions':0,'conflicts':0,'theory_lemmas':0,'resolutions':0,'backjumps':0}
    def literal_value(l):
        v=val.get(abs(l))
        return None if v is None else (v if l>0 else not v)
    def enqueue(l,r):
        v=abs(l)
        if v in val:return val[v]==(l>0)
        val[v]=l>0;level[v]=dl;reason[v]=r;trail.append(l)
        return True
    while True:
        conflict=None
        # Scanning propagation reaches a Boolean fixed point before theory.
        while True:
            progress=False
            for i,c in enumerate(clauses):
                values=[literal_value(l) for l in c]
                if any(v is True for v in values):continue
                unknown=[l for l in c if literal_value(l) is None]
                if not unknown:conflict=i;break
                if len(unknown)==1:
                    enqueue(unknown[0],i);progress=True
            if conflict is not None or not progress:break
        if conflict is None:
            cycle,model=difference_check(trail,atoms,nodes)
            if cycle is not None:
                conflict=append((-l for l in cycle),'theory',cycle=cycle)
                stats['theory_lemmas']+=1
        if conflict is not None:
            stats['conflicts']+=1
            if stats['conflicts']>max_conflicts:
                return {'status':'unknown','stats':stats}
            c=clauses[conflict]
            while c:
                high=max(level[abs(l)] for l in c)
                at_high=[l for l in c if level[abs(l)]==high]
                if high>0 and len(at_high)==1:break
                # Latest implication on the highest conflicting level.
                pivot_var=next(abs(l) for l in reversed(trail)
                    if -l in c and level[abs(l)]==high and reason[abs(l)] is not None)
                assigned=pivot_var if val[pivot_var] else -pivot_var
                r=reason[pivot_var]
                c=resolve(c,clauses[r],-assigned)
                conflict=append(c,'resolution',left=conflict,right=r,pivot=-assigned)
                stats['resolutions']+=1
            if not c:
                return {'status':'unsat','proof':proofs,'root':conflict,'stats':stats}
            high=max(level[abs(l)] for l in c)
            asserting=next(l for l in c if level[abs(l)]==high)
            back=max((level[abs(l)] for l in c if l!=asserting),default=0)
            if back<dl-1:stats['backjumps']+=1
            for l in list(trail):
                v=abs(l)
                if level[v]>back:
                    del val[v];del level[v];del reason[v]
            trail=[l for l in trail if abs(l) in val];dl=back
            for l in c:activity[abs(l)]+=1
            enqueue(asserting,conflict)
            continue
        if len(val)==len(variables):
            return {'status':'sat','assignment':{str(v):b for v,b in val.items()},
                    'values':model,'stats':stats}
        v=max((v for v in variables if v not in val),key=lambda v:(activity[v],-v))
        dl+=1;stats['decisions']+=1;enqueue(v,None)

def verify_unsat(cnf,atoms,nodes,result):
    """Independent replay: no SAT search, propagation, or Bellman-Ford."""
    try:
        if result['status']!='unsat':return False
        checked=[]
        for i,p in enumerate(result['proof']):
            c=frozenset(p['clause'])
            if any(type(l) is not int or l==0 for l in c):return False
            if p['kind']=='input':
                j=p['index']
                if type(j) is not int or not 0<=j<len(cnf) or c!=frozenset(cnf[j]):return False
            elif p['kind']=='theory':
                cycle=p['cycle'];balance=[0]*nodes;bound=0
                if not cycle or c!=frozenset(-l for l in cycle):return False
                for l in cycle:
                    if type(l) is not int or l==0:return False
                    u,v,k=atoms[abs(l)]
                    if l<0:u,v,k=v,u,-k-1
                    if not 0<=u<nodes or not 0<=v<nodes:return False
                    balance[u]-=1;balance[v]+=1;bound+=k
                if any(balance) or bound>=0:return False
            elif p['kind']=='resolution':
                left,right=p['left'],p['right'];pivot=p['pivot']
                if type(left) is not int or type(right) is not int or not 0<=left<i or not 0<=right<i:return False
                a,b=checked[left],checked[right]
                if pivot not in a or -pivot not in b:return False
                if c != frozenset((a-{pivot}) | (b-{-pivot})):return False
            else:return False
            checked.append(c)
        root=result['root']
        return type(root) is int and 0<=root<len(checked) and not checked[root]
    except (KeyError,ValueError,TypeError,IndexError):return False

def verify_sat(cnf,atoms,nodes,result):
    try:
        if result['status']!='sat':return False
        values=result['values'];a={int(v):b for v,b in result['assignment'].items()}
        if len(values)!=nodes or any(type(v) is not int for v in values):return False
        if any(type(b) is not bool for b in a.values()):return False
        for v,(i,j,c) in atoms.items():
            if a[v] != (values[j]-values[i]<=c):return False
        return all(any(a[abs(l)]==(l>0) for l in clause) for clause in cnf)
    except (KeyError,ValueError,TypeError,IndexError):return False

def exhaustive_oracle(cnf,atoms,nodes):
    """Boolean enumeration + independent Floyd-Warshall (small tests only)."""
    vs=sorted(set(abs(l) for c in cnf for l in c)|set(atoms))
    for bits in product((False,True),repeat=len(vs)):
        a=dict(zip(vs,bits))
        if not all(any(a[abs(l)]==(l>0) for l in c) for c in cnf):continue
        d=[[None]*nodes for _ in range(nodes)]
        for i in range(nodes):d[i][i]=0
        for v,(i,j,c) in atoms.items():
            if not a[v]:i,j,c=j,i,-c-1
            d[i][j]=c if d[i][j] is None else min(d[i][j],c)
        for k in range(nodes):
            for i in range(nodes):
                for j in range(nodes):
                    if d[i][k] is not None and d[k][j] is not None:
                        w=d[i][k]+d[k][j]
                        d[i][j]=w if d[i][j] is None else min(d[i][j],w)
        if all(d[i][i]>=0 for i in range(nodes)):return True
    return False

def pigeonhole(pigeons,holes):
    def v(i,j):return i*holes+j+1
    clauses=[[v(i,j) for j in range(holes)] for i in range(pigeons)]
    for j in range(holes):
        for i in range(pigeons):
            for k in range(i+1,pigeons):clauses.append([-v(i,j),-v(k,j)])
    return clauses
