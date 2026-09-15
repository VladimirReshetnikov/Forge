"""Exact reachable-space search; no assumptions about search appear in check.py."""
from fractions import Fraction as Q
from collections import deque
from .exact import encvec,encmat,rowmul,dot,encq

class Echelon:
    def __init__(self,d): self.d=d; self.rows=[]; self.combinations=[]; self.pivots=[]; self.basis=[]
    def reduce(self,v):
        y=list(v); coeff=[Q(0)]*self.d
        for row,comb,p in zip(self.rows,self.combinations,self.pivots):
            a=y[p]
            if a:
                y=[x-a*z for x,z in zip(y,row)]
                coeff=[x+a*z for x,z in zip(coeff,comb)]
        return y,coeff
    def admit(self,v):
        rem,c=self.reduce(v)
        if not any(rem): return False
        p=next(i for i,x in enumerate(rem) if x); pivot=rem[p]; r=len(self.basis)
        rep=[-x/pivot for x in c]; rep[r]=1/pivot
        self.rows.append([x/pivot for x in rem]); self.combinations.append(rep); self.pivots.append(p)
        self.basis.append(list(v)); return True
    def coordinates(self,v):
        rem,c=self.reduce(v)
        if any(rem): raise ValueError('vector outside discovered space')
        return c[:len(self.basis)]

def model(u,matrices,v):
    d=len(u)
    if d==0 or len(v)!=d or any(len(m)!=d or any(len(row)!=d for row in m) for m in matrices):
        raise ValueError('invalid dimensions')
    return {'kind':'linear-word','dimension':d,'initial':encvec(u),'output':encvec(v),'transitions':[encmat(m) for m in matrices]}

def search(u,matrices,v):
    """Complete for this exact finite rational model, absent resource interruption.
    A negative result is a concrete word, never failure to find a certificate.
    """
    d=len(u); u=list(map(Q,u)); v=list(map(Q,v)); matrices=[[[Q(x) for x in row] for row in m] for m in matrices]
    e=Echelon(d); agenda=deque(); words=[]; expanded=0
    if dot(u,v): return {'kind':'separating-word','word':[],'value':encq(dot(u,v))},{'basis_rank':0,'expansions':0}
    if e.admit(u): agenda.append(0); words.append([])
    while agenda:
        i=agenda.popleft()
        for a,m in enumerate(matrices):
            w=words[i]+[a]; y=rowmul(e.basis[i],m); expanded+=1
            value=dot(y,v)
            if value: return {'kind':'separating-word','word':w,'value':encq(value)},{'basis_rank':len(e.basis),'expansions':expanded}
            if e.admit(y): words.append(w); agenda.append(len(e.basis)-1)
    cert={'kind':'linear-closure','basis':encmat(e.basis),'initial_coordinates':encvec(e.coordinates(u)),
          'actions':[encmat([e.coordinates(rowmul(b,m)) for b in e.basis]) for m in matrices]}
    return cert,{'basis_rank':len(e.basis),'expansions':expanded}

def polynomial_input_search(u,coefficient_matrices,v):
    """Decide all rational input words via a degree+1 interpolation alphabet.
    Return a direct coefficient-closure certificate, or actual grid inputs.
    """
    D=len(coefficient_matrices)-1; d=len(u)
    values=[[[sum(Q(coefficient_matrices[h][i][j])*x**h for h in range(D+1)) for j in range(d)] for i in range(d)] for x in range(D+1)]
    c,stats=search(u,values,v)
    if c['kind']=='separating-word':
        return c,stats # alphabet indices ARE the concrete rational grid values
    e=Echelon(d)
    from .exact import rational
    for row in c['basis']: e.admit([rational(x) for x in row])
    c['actions']=[encmat([e.coordinates(rowmul(b,m)) for b in e.basis]) for m in coefficient_matrices]
    return c,stats
