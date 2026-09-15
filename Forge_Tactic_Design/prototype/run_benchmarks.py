"""Reproducible synthetic experiments. These are NOT comparisons against Lean.

Run from prototype/: python run_benchmarks.py --output ../results
Search time is measured separately where convenient; all accepted certificates
are checked exactly. Dataset construction deliberately targets covered fragments.
"""
from __future__ import annotations
import argparse,csv,json,platform,random,sys,time
from pathlib import Path
from fractions import Fraction as Q
from dataclasses import asdict
import numpy,scipy,sympy
from forge.polynomial import Poly
from forge.nonlinear import discover
from forge.checkers import check_cone,check_invariant,check_bernstein
from forge.bernstein import discover as bernstein,leaves
from forge.invariants import additive_invariant
from forge.demand import Term,Atom,Rule,demand_prove,forward_prove,check_horn


def cone_json(c):
    return {'terms':[{'weight':str(t.weight),'square':t.square.to_json(),'factors':list(t.factors)} for t in c.terms],
            'ideal':[p.to_json() for p in c.ideal]}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path,default=Path('../results'))
    args=ap.parse_args(); args.output.mkdir(parents=True,exist_ok=True)
    rng=random.Random(20260914); data={}
    data['environment']={'python':sys.version,'platform':platform.platform(),
                         'numpy':numpy.__version__,'scipy':scipy.__version__,'sympy':sympy.__version__,
                         'seed':20260914,'lean_runtime':'unavailable; not executed',
                         'comparison_scope':'Python synthetic algorithms, not Lean grind'}
    data['horn']=[]
    for depth in [4,8,10,12,14]:
        x,a=Term('?x'),Term('a'); P=lambda t:Atom('P',(t,))
        rules=(Rule('grow_g',P(Term('g',(x,))),(P(x),)),Rule('grow_f',P(Term('f',(x,))),(P(x),)))
        t=a
        for _ in range(depth):t=Term('f',(t,))
        facts=(P(a),); goal=P(t)
        row={'depth':depth}
        for name,fn in [('forward',forward_prove),('demand',demand_prove)]:
            start=time.perf_counter(); r=fn(facts,rules,goal,max_depth=depth,max_facts=200000) if name=='forward' else fn(facts,rules,goal,max_depth=depth)
            seconds=time.perf_counter()-start
            assert r.certificate and check_horn(facts,rules,goal,r.certificate)
            row.update({name+'_facts':r.terms_or_facts,name+'_instances':r.instances,
                        name+'_seconds':seconds,name+'_proof_nodes':len(r.certificate.nodes)})
        data['horn'].append(row)
    data['cone_named']=[]; certs=[]
    def named(name,p,gs=(),es=(),degree=4,expected='proved'):
        r=discover(p,gs,es,degree=degree)
        assert r.status==expected,(name,r.status,r.reason)
        checked=bool(r.certificate and check_cone(p,gs,es,r.certificate))
        data['cone_named'].append({'name':name,'degree_cap':degree,'status':r.status,'generators':r.generators,
                                  'search_seconds':r.seconds,'checked':checked,
                                  'terms':len(r.certificate.terms) if r.certificate else None,
                                  'reason':r.reason})
        if checked:
            certs.append({'name':name,'target':p.to_json(),'nonnegative':[g.to_json() for g in gs],
                          'equal_zero':[e.to_json() for e in es], 'certificate':cone_json(r.certificate)})
    x,y=[Poly.variable(2,i) for i in range(2)]
    named('shifted_square',(x-7)**2,degree=2)
    named('two_variable_AMGM',x*x+y*y-2*x*y,degree=2)
    named('box_cubic',x*y*(1-x),(x,1-x,y,1-y),degree=3)
    named('box_quartic',x*y*(1-x)*(1-y),(x,1-x,y,1-y),degree=4)
    named('box_quartic_cap2',x*y*(1-x)*(1-y),(x,1-x,y,1-y),degree=2,expected='unknown')
    named('equality_ideal',y*y-2*x+1,(),(y-x,),degree=2)
    named('rational_margin',(x-Q(2,3))**2+Q(1,97),degree=2)
    named('false_near_square',(x-Q(2,3))**2-Q(1,1000000),degree=2,expected='unknown')
    a,b,c,d=[Poly.variable(4,i) for i in range(4)]
    named('Cauchy_Schwarz_2',(a*a+b*b)*(c*c+d*d)-(a*c+b*d)**2,degree=4)
    x,y,z=[Poly.variable(3,i) for i in range(3)]
    named('lower_bound_cubic',(x-1)*(y-2)*(z-3),(x-1,y-2,z-3),degree=3)
    named('three_variable_variance',x*x+y*y+z*z-x*y-y*z-z*x,degree=2)
    x,y=[Poly.variable(2,i) for i in range(2)]
    named('Motzkin_true_outside_SOS',x**4*y*y+x*x*y**4+1-3*x*x*y*y,degree=6,expected='unknown')
    data['cone_generated']=[]
    gs=(x,1-x,y,1-y)
    for i in range(100):
        p=Poly.constant(2,0)
        for _ in range(6):
            term=Poly.constant(2,Q(rng.randint(1,5),rng.randint(1,5)))
            for _ in range(rng.randint(0,4)):
                term*=rng.choice(gs)
            p+=term
        r=discover(p,gs,degree=4)
        assert r.certificate and check_cone(p,gs,(),r.certificate)
        data['cone_generated'].append({'case':i,'status':r.status,'generators':r.generators,
                                       'terms':len(r.certificate.terms),'seconds':r.seconds})
    data['negative_controls']=[]
    x=Poly.variable(1,0)
    for i in range(24):
        a=Q(rng.randint(-10,10),rng.randint(1,7)); eps=Q(1,rng.randint(10,1000000))
        p=(x-a)**2-eps; r=discover(p,degree=2)
        assert p.eval([a])<0 and r.status=='unknown'
        data['negative_controls'].append({'case':i,'witness':str(a),'value':str(p.eval([a])),
                                           'status':r.status,'seconds':r.seconds})
    data['bernstein']=[]
    box=((Q(0),Q(1)),)
    cases=[('positive_needs_split',x*x-x+Q(1,3),8,True),
           ('nonnegative_box',x*(1-x),8,True),
           ('dyadic_zero',(x-Q(1,2))**2,8,True),
           ('nondyadic_zero_true_unknown',(x-Q(1,3))**2,8,False),
           ('false_negative_midpoint',x*x-x+Q(1,5),8,False)]
    for i in range(40):
        a=Q(rng.randint(0,30),30); eps=Q(1,rng.randint(10,500))
        cases.append((f'positive_quadratic_{i}',(x-a)**2+eps,10,True))
    for name,p,depth,expected in cases:
        start=time.perf_counter(); c=bernstein(p,box,depth=depth); search=time.perf_counter()-start
        assert (c is not None)==expected,name
        start=time.perf_counter(); check=bool(c and check_bernstein(p,box,c)); ct=time.perf_counter()-start
        assert not c or check
        data['bernstein'].append({'name':name,'status':'proved' if c else 'unknown','leaves':leaves(c) if c else None,
                                  'search_seconds':search,'check_seconds':ct,'checked':check})
    data['invariants']=[]; inv_certs=[]
    increments=[(f'power_{k}',(x+1)**k,Q(0)) for k in range(9)]
    for i in range(40):
        p=Poly.make(1,[((k,),Q(rng.randint(-7,7),rng.randint(1,5))) for k in range(rng.randint(1,7))])
        increments.append((f'random_{i}',p,Q(rng.randint(-5,5))))
    for name,p,initial in increments:
        start=time.perf_counter(); c=additive_invariant(p,initial=initial); search=time.perf_counter()-start
        assert c and check_invariant(c)
        data['invariants'].append({'name':name,'increment_degree':p.degree,'invariant_degree':c.invariant.degree,
                                   'status':'proved','seconds':search})
        inv_certs.append({'name':name,'increment':p.to_json(),'invariant':c.invariant.to_json(),
                          'initial':list(map(str,c.initial)),'transition':[t.to_json() for t in c.transition]})
    (args.output/'benchmarks.json').write_text(json.dumps(data,indent=2)+'\n')
    (args.output/'cone_certificates.json').write_text(json.dumps(certs,indent=2)+'\n')
    (args.output/'invariant_certificates.json').write_text(json.dumps(inv_certs,indent=2)+'\n')
    for name in ['horn','cone_named','cone_generated','negative_controls','bernstein','invariants']:
        with (args.output/f'{name}.csv').open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=list(data[name][0]));writer.writeheader();writer.writerows(data[name])
    summary={
      'horn_cases':len(data['horn']),
      'largest_horn':data['horn'][-1],
      'named_cone_proved':sum(r['status']=='proved' for r in data['cone_named']),
      'named_cone_total':len(data['cone_named']),
      'generated_cone_proved':len(data['cone_generated']),
      'negative_controls_accepted':0,
      'negative_controls_total':len(data['negative_controls']),
      'bernstein_proved':sum(r['status']=='proved' for r in data['bernstein']),
      'bernstein_total':len(data['bernstein']),
      'invariants_proved':len(data['invariants']),
      'lean_comparison':'NOT RUN'
    }
    (args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
