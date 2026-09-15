#!/usr/bin/env python3
"""Supplemental symbolic check of the paper's universal-q squared-binomial formula.
Unlike replay.py this small check uses SymPy. It is not a Lean proof and is not
counted in the 245-entry rational-problem corpus.
"""
import json
import sympy as s
n,k,q=s.symbols('n k q')
r=2;p=2
a=[(q-1)**2*(n+1),-(q+1)*(2*n+3),n+2]
f=[(q-1)*(n+1),2*k-3*n-6]
rn=[s.prod(n+h for h in range(1,i+1))**p*s.prod(n+h-k for h in range(i+1,r+1))**p for i in range(r+1)]
res=sum(ai*ri for ai,ri in zip(a,rn))
for j,pj in enumerate(f):
    rm=k**p*s.prod(n+h for h in range(1,j+1))**p*s.prod(n+h-k for h in range(j+2,r+1))**p
    res += -q*pj.subs(k,k+1)*rn[j]+pj*rm
assert s.expand(res)==0
boundary=[]
def b(j,t):
    d=j-t
    return s.Integer(0) if d<0 else s.prod(n+j-h for h in range(d))*s.Rational(1,s.factorial(d))
for t in range(1,r+1):
    z=sum(a[i]*b(i,t)**p for i in range(r+1))
    z+=sum(-q*f[j].subs(k,n+t+1)*b(j,t)**p+f[j].subs(k,n+t)*b(j,t-1)**p for j in range(r))
    boundary.append(str(s.expand(z)));assert s.expand(z)==0
print(json.dumps({'status':'PASS','sympy':s.__version__,'interior_residual':str(s.expand(res)),
                  'boundary_residuals':boundary,'lean_status':'NOT_RUN'},indent=2))
