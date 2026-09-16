#!/usr/bin/env python3
"""Optional, independent symbolic/numerical diagnostics; not proof authority.

SymPy checks Taylor coefficients and differential/polynomial identities.
mpmath samples enclosure claims, never deciding their universal validity.
"""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
from fractions import Fraction as Q
import sympy as S
import mpmath as M
ROOT=Path(__file__).resolve().parents[1]
x=S.Symbol('x',real=True)
def sq(q):
    q=Q(q);return S.Rational(q.numerator,q.denominator)
def mq(q):
    q=Q(q);return M.mpf(q.numerator)/q.denominator
def sp(p):return sum(sq(v)*x**k for k,v in enumerate(p))
def expr(e):
    op=e[0]
    if op=='poly':return sp(e[1])
    if op=='neg':return -expr(e[1])
    if op=='add':return expr(e[1])+expr(e[2])
    if op=='mul':return expr(e[1])*expr(e[2])
    y=sq(e[1])*x
    return {'exp':S.exp,'sin':S.sin,'cos':S.cos,'atan':S.atan}.get(op,lambda z:S.log(1+z))(y)
def mp_expr(e,t):
    op=e[0]
    if op=='poly':return sum(mq(v)*t**k for k,v in enumerate(e[1]))
    if op=='neg':return -mp_expr(e[1],t)
    if op=='add':return mp_expr(e[1],t)+mp_expr(e[2],t)
    if op=='mul':return mp_expr(e[1],t)*mp_expr(e[2],t)
    y=mq(e[1])*t
    return {'exp':M.exp,'sin':M.sin,'cos':M.cos,'atan':M.atan}.get(op,M.log1p)(y)
def ep(rows):return sum(sp(p)*S.exp(sq(a)*x) for a,p in rows)
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'reproduced-oracle.json');args=p.parse_args()
    cs=json.loads((ROOT/'results/run-01/certificates.json').read_text())
    counts={'taylor_polynomial_identities':0,'sampled_remainder_enclosures':0,
            'differential_identities':0,'shifted_tail_identities':0}
    M.mp.dps=120
    for id,c in cs.items():
        subj=c['subject'];kind=c['kind']
        if kind=='anchored':
            f=expr(subj['expr']);k=c['order']
            expansion=S.series(f,x,0,k).removeO().expand()
            assert S.expand(expansion-sp(c['polynomial']))==0,id
            counts['taylor_polynomial_identities']+=1
            b=mq(subj['b']);lo,hi=map(mq,c['error'])
            for t in (Q(1,1000000),Q(1,32),Q(1,16),Q(1,8),Q(1,4),Q(1,3),Q(1,2),Q(2,3),Q(3,4),Q(1)):
                z=b*mq(t)
                value=mp_expr(subj['expr'],z)
                approx=sum(mq(v)*z**j for j,v in enumerate(c['polynomial']))
                r=(value-approx)/z**k
                assert lo-M.mpf('1e-70') <= r <= hi+M.mpf('1e-70'),(id,t,r,lo,hi)
                counts['sampled_remainder_enclosures']+=1
        elif kind=='ladder':
            for i,a in enumerate(c['rates']):
                f=ep(c['stages'][i]);g=ep(c['stages'][i+1])
                assert S.expand(S.diff(f,x)-sq(a)*f-g)==0,id
                counts['differential_identities']+=1
        else:
            num,den=sp(subj['numerator']),sp(subj['denominator']);N=c['cutoff']
            assert S.expand(den.subs(x,x+N)-sp(c['shifted_denominator']))==0,id
            if kind=='barrier':
                s,power,C=c['shift'],c['power'],sq(c['constant'])
                u,v=(x+s)**power,(x+s+1)**power
                residual=C*(v-u)*den-num*u*v
                assert S.expand(num.subs(x,x+N)-sp(c['shifted_numerator']))==0,id
            else:residual=x*num-sq(c['minorant'])*den
            assert S.expand(residual.subs(x,x+N)-sp(c['shifted_residual']))==0,id
            counts['shifted_tail_identities']+=1
    report={'sympy':S.__version__,'mpmath':M.__version__,'decimal_precision':120,'counts':counts,
            'status':'all assertions passed','evidence':'Symbolic cross-checks and sampled numeric diagnostics; not universal proofs'}
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
