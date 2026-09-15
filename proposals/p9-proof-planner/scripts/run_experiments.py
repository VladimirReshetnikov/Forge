#!/usr/bin/env python3
"""Run mechanism benchmarks; this never invokes or emulates Lean's grind."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from fractions import Fraction as Q
import json, csv, platform, time
import numpy, scipy, sympy, pytest
from forge_lab.poly import Poly, check_cone, check_box, ConeCertificate, ConeTerm
from forge_lab.nonlinear import cone_search, box_search
from forge_lab.induction import synthesize_accumulator, prove_induction, EqGoal
from forge_lab.terms import V, F
from forge_lab.horn import branching_problem, forward, backward, check_horn
from forge_lab.witness import synthesize_majorant


def main():
    dest=ROOT/'results'; dest.mkdir(exist_ok=True)
    certificates=[]; results={'environment':{
        'python':platform.python_version(),'platform':platform.platform(),
        'numpy':numpy.__version__,'scipy':scipy.__version__,'sympy':sympy.__version__,
        'pytest':pytest.__version__, 'lean_execution':'NOT RUN; runtime unavailable',
        'measurement':'Single local run; mechanism demonstrations, not a Lean comparison'}}
    bank,istats=synthesize_accumulator(); results['induction']=istats
    xs,ys=V('xs'),V('ys')
    for name,g,gen in [
      ('rev_append',EqGoal(F('rev',F('app',xs,ys)),F('app',F('rev',ys),F('rev',xs))),('?ys',)),
      ('rev_invol',EqGoal(F('rev',F('rev',xs)),xs),())]:
        c=prove_induction(g,'?xs',bank.rules,gen)
        if c is None or not bank.add(name,g,c): raise RuntimeError(name)
    certificates.append({'kind':'theorem_bank','lemmas':[
        {'name':n,'goal':g.json(),'certificate':c.json()}
        for n,(g,c) in bank.certificates.items()], 'specialization':istats['specialization']})
    results['induction']['checked_lemmas']=list(bank.certificates)
    results['horn']=[]
    for depth in (4,8,12,16):
        g,fs,rs=branching_problem(depth)
        t=time.perf_counter(); f,ss=forward(g,fs,rs,node_cap=5000)
        ft=time.perf_counter()-t
        t=time.perf_counter(); b,bs=backward(g,fs,rs)
        bt=time.perf_counter()-t
        if b is None or not check_horn(g,fs,rs,b): raise RuntimeError('horn replay')
        if f is not None and not check_horn(g,fs,rs,f): raise RuntimeError('forward replay')
        results['horn'].append({'depth':depth,'forward':ss,'backward':bs,
                                'forward_seconds':ft,'backward_seconds':bt})
        certificates.append({'kind':'horn','depth':depth,'goal':g.json(),
            'facts':[a.json() for a in fs],
            'rules':[{'name':r.name,'head':r.head.json(),'body':[a.json() for a in r.body]} for r in rs],
            'proof':[n.json() for n in b]})
    x,y,z=[Poly.var(3,i) for i in range(3)]
    cases=[('quartic',x**4+y**4+z**4-x*x*y*y-y*y*z*z-z*z*x*x,()),
        ('product',x*y,(x,y)),('cube',x**3,(x,)),
        ('unit_interval',x-x*x,(x,1-x)),
        ('guarded_cubic',x**3+y**3-x*y*(x+y),(x,y))]
    results['nonlinear']=[]
    for name,p,gs in cases:
        c,s=cone_search(p,gs)
        if c is None or not check_cone(p,gs,c): raise RuntimeError(name)
        results['nonlinear'].append({'name':name,'polynomial':str(p),**s})
        certificates.append({'kind':'cone','name':name,'target':p.json(),
            'guards':[g.json() for g in gs],'certificate':c.json()})
    u,v=Poly.var(2,0),Poly.var(2,1); p=(u+v+1)**2
    c,s=cone_search(p)
    direct=ConeCertificate((ConeTerm(Q(1),u+v+1),))
    assert c is None and check_cone(p,(),direct)
    results['dictionary_control']={'polynomial':str(p),'search':s,
        'independent_supplied_certificate_checked':True}
    certificates.append({'kind':'cone','name':'supplied_three_term_square','target':p.json(),
        'guards':[],'certificate':direct.json()})
    x=Poly.var(1,0); p=x*x-x+Q(3,10); box=((Q(0),Q(1)),)
    c,s=box_search(p,box,strict=True)
    if c is None or not check_box(p,box,c,strict=True): raise RuntimeError('box')
    results['bernstein']={'polynomial':str(p),**s}
    certificates.append({'kind':'box','target':p.json(),'box':[['0','1']],
                         'strict':True,'certificate':c.json()})
    w,cs,s=synthesize_majorant()
    if w is None or cs is None: raise RuntimeError('witness')
    results['witness']=s
    certificates.append({'kind':'witness','witness':w.json(),
                          'minus':cs[0].json(),'plus':cs[1].json()})
    (dest/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    (dest/'certificates.json').write_text(json.dumps(certificates,indent=2)+'\n')
    with (dest/'horn_counts.csv').open('w',newline='') as f:
        wr=csv.writer(f); wr.writerow(['depth','forward_generated','backward_proof_nodes','forward_status','backward_status'])
        for r in results['horn']:
            wr.writerow([r['depth'],r['forward']['generated'],r['backward']['proof_nodes'],r['forward']['status'],r['backward']['status']])
    print(json.dumps(results,indent=2))

if __name__=='__main__': main()
