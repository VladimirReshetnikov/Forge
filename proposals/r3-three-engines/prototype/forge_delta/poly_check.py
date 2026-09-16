"""Projection checker. Does not import or run Fourier--Motzkin search.

Checks both directions: nonnegative row combinations, and coverage of every
zero row/lower-upper pair. A published row can be shared among many pairs.
"""
from fractions import Fraction as F
from .wire import q, require

def parse(r,n):
    require(set(r)=={'a','strict'} and type(r['strict']) is bool)
    require(len(r['a'])==n+1)
    return tuple(map(q,r['a'])),r['strict']

def combine(rs,w,n):
    require(len(rs)==len(w))
    w=tuple(map(q,w)); require(all(a>=0 for a in w))
    a=[F(0)]*(n+1); s=False
    for (b,t),c in zip(rs,w):
        for k in range(n+1): a[k]+=c*b[k]
        s=s or (c>0 and t)
    return tuple(a),bool(s)

def proportion(a,b):
    # b must be a strictly positive scalar multiple of a, including the zero case.
    nz=next((i for i,x in enumerate(a) if x),None)
    if nz is None: return not any(b)
    c=b[nz]/a[nz]
    return c>0 and all(y==c*x for x,y in zip(a,b))

def contradiction(rs,w,n):
    a,s=combine(rs,w,n)
    return not any(a[:-1]) and (a[-1]<0 or s and a[-1]==0)

def eval_row(r,x):
    a,s=r; z=a[-1]
    for k,c in enumerate(a[:-1]): z+=c*x[k]
    return z>0 if s else z>=0

def check(problem,cert):
    try:
        n,p=problem['variables'],problem['parameters']
        require(type(n) is int and type(p) is int and 0<=p<=n<=20)
        rows=[parse(r,n) for r in problem['target']]
        dom=[parse(r,n) for r in problem['domain']]
        require(all(not any(a[p:-1]) for a,_ in dom))
        require(len(cert['steps'])==n-p)
        for v,st in zip(reversed(range(p,n)),cert['steps']):
            require(type(st['var']) is int and st['var']==v)
            out=[]
            for o in st['outputs']:
                r=parse(o['row'],n)
                require(r==combine(rows,o['weights'],n))
                require(r[0][v]==0)
                out.append(r)
            needed={('zero',i) for i,(a,_) in enumerate(rows) if a[v]==0}
            needed|={('pair',i,j) for i,(a,_) in enumerate(rows) if a[v]>0
                                 for j,(b,_) in enumerate(rows) if b[v]<0}
            seen=set()
            for ob in st['required']:
                key=(ob['kind'],ob['i']) if ob['kind']=='zero' else (ob['kind'],ob['i'],ob['j'])
                require(key in needed and key not in seen); seen.add(key)
                k=ob['out']; require(type(k) is int and 0<=k<len(out))
                a,s=rows[ob['i']]
                if key[0]=='pair':
                    b,t=rows[ob['j']]
                    expect=tuple(a[l]/a[v]-b[l]/b[v] for l in range(n+1))
                    strict=s or t
                else: expect,strict=a,s
                require(out[k][1]==strict and proportion(expect,out[k][0]))
            require(seen==needed)
            rows=out
        require(all(not any(a[p:-1]) for a,_ in rows))
        if cert['kind']=='proved':
            require(cert['witness_rule']=='extrema-v1')
            require(len(cert['domain_proofs'])==len(rows))
            for (a,s),w in zip(rows,cert['domain_proofs']):
                require(contradiction(dom+[(tuple(-x for x in a),not s)],w,n))
        elif cert['kind']=='refuted':
            require(len(cert['parameters'])==p)
            x=list(map(q,cert['parameters']))+[F(0)]*(n-p)
            require(all(eval_row(r,x) for r in dom))
            i=cert['bad_row']; require(type(i) is int and 0<=i<len(rows))
            require(not eval_row(rows[i],x))
        else: return False
        return True
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OverflowError):
        return False
