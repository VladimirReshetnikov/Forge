#!/usr/bin/env python3
"""Reproducible experiments; use --out to avoid replacing recorded evidence."""
import argparse,copy,csv,json,platform,random,sys,time
from pathlib import Path
from fractions import Fraction as F
from math import comb,factorial
from forge_delta import poly_search as ps, poly_check as pc
from forge_delta import poly_witness as pw
from forge_delta import nc_search as ns, nc_check as nc
from forge_delta import analytic_search as an, analytic_check as ac
from tests.oracles import bounded_feasible,weyl_zero

SEED=20260915

def corner(a=F(1),coupled=False):
    p={'parameters':2,'variables':3,'domain':[
        ps.row([1,0,0,0]),ps.row([-1,0,0,a]),ps.row([0,1,0,0]),ps.row([0,-1,0,a])],
        'target':[ps.row([0,0,1,0]),ps.row([-1,-1,1,a]),ps.row([1,0,-1,0]),ps.row([0,1,-1,0])]}
    if coupled:
        for key in ('domain','target'):
            for r in p[key]: r['a'].insert(3,'0')
        p['variables']=4
        p['target'] += [ps.row([-1,0,-2,1,0]),ps.row([1,0,2,-1,0])]
    return p

def first_leaf(tree):
    while tree['kind']=='split': tree=tree['left']
    return tree

def experiment(out):
    rng=random.Random(SEED); out.mkdir(parents=True,exist_ok=True)
    records=[]; metrics=[]; mutations=[]; checks=[]
    def run(lane,name,p,producer,checker,expected):
        t=time.perf_counter(); c=producer(p); search_ms=(time.perf_counter()-t)*1000
        t=time.perf_counter(); ok=checker(p,c); check_ms=(time.perf_counter()-t)*1000
        assert c['kind']==expected,(name,c)
        assert ok==(expected!='unknown'),(name,'replay failed',c)
        entry={'lane':lane,'name':name,'problem':p,'certificate':c}; records.append(entry)
        metrics.append({'lane':lane,'name':name,'outcome':c['kind'],'search_ms':search_ms,
                        'check_ms':check_ms,'certificate_bytes':len(json.dumps(c,sort_keys=True).encode())})
        return c
    def reject(lane,name,p,c,checker):
        assert not checker(p,c),(name,'invalid mutation accepted')
        mutations.append({'lane':lane,'name':name,'accepted':False})

    # Piecewise witnesses, including simultaneous output reconstruction.
    witness_evaluations=0
    for i in range(40):
        a=F(rng.randint(1,9),rng.randint(1,7)); p=corner(a,i%2==1)
        c=run('poly',f'corner-{i:02}',p,ps.prove,pc.check,'proved')
        dag=pw.compile_witness(p,c)
        if i==0:
            (out/'corner-witness-dag.json').write_text(json.dumps(dag,indent=2)+'\n')
            (out/'corner-witness-uncompiled.lean.txt').write_text(pw.lean_expression(dag)+'\n')
        for j in range(10):
            x,y=a*F(rng.randrange(17),16),a*F(rng.randrange(17),16)
            z=pw.evaluate(dag,[x,y]); assert z==ps.witness(p,c,[x,y])
            assert all(pc.eval_row(pc.parse(r,p['variables']),[x,y]+z) for r in p['target'])
            witness_evaluations+=1
        m=copy.deepcopy(c); m['steps'][0]['var']+=1; reject('poly',f'wrong-variable-{i}',p,m,pc.check)
        m=copy.deepcopy(c); m['steps'][0]['required'].pop(); reject('poly',f'missing-pair-{i}',p,m,pc.check)
        m=copy.deepcopy(c); m['steps'][-1]['outputs'][0]['row']['a'][-1]=str(F(m['steps'][-1]['outputs'][0]['row']['a'][-1])+1)
        reject('poly',f'wrong-row-{i}',p,m,pc.check)
    for i in range(30):
        a=F(rng.randint(1,9),rng.randint(1,7))
        p={'parameters':1,'variables':2,'domain':[],
           'target':[ps.row([-1,1,0],True),ps.row([1,-1,a],True)]}
        c=run('poly',f'strict-{i:02}',p,ps.prove,pc.check,'proved')
        for x in (F(-11),F(0),F(13,7)):
            z=pw.evaluate(pw.compile_witness(p,c),[x]); assert x<z[0]<x+a; witness_evaluations+=1
        m=copy.deepcopy(c); m['steps'][0]['outputs'][0]['row']['strict']=False
        reject('poly',f'lost-strictness-{i}',p,m,pc.check)
    # Feasible touching extrema with a nonactive strict lower bound.
    p={'parameters':0,'variables':1,'domain':[],
       'target':[ps.row([1,0],True),ps.row([1,-1]),ps.row([-1,1])]}
    c=run('poly','mixed-touching',p,ps.prove,pc.check,'proved')
    assert ps.witness(p,c,[])==[F(1)]
    # One-sided strict/unbounded and unconstrained output variables.
    for name,rs in [('strict-lower',[ps.row([1,0],True)]),('strict-upper',[ps.row([-1,0],True)]),('unconstrained',[])]:
        p={'parameters':0,'variables':1,'domain':[],'target':rs}
        c=run('poly',name,p,ps.prove,pc.check,'proved'); pw.compile_witness(p,c)
    for i in range(30):
        a=F(rng.randint(1,9),rng.randint(1,7))
        p={'parameters':1,'variables':2,'domain':[ps.row([1,0,1]),ps.row([-1,0,1])],
           'target':[ps.row([-1,1,0]),ps.row([1,-1,-a])]}
        c=run('poly',f'counterexample-{i:02}',p,ps.prove,pc.check,'refuted')
        m=copy.deepcopy(c); m['bad_row']=len(c['steps'][-1]['outputs'])
        reject('poly',f'bad-refutation-row-{i}',p,m,pc.check)
    for i in range(5):
        p={'parameters':1,'variables':2,'domain':[ps.row([1,0,0],True),ps.row([-1,0,0])],
           'target':[ps.row([0,1,-i-1]),ps.row([0,-1,0])]}
        run('poly',f'empty-domain-{i}',p,ps.prove,pc.check,'proved')
    run('poly','pair-budget-control',corner(),lambda p:ps.prove(p,limit=0),pc.check,'unknown')

    # Independent exact bounded-feasibility oracle (not the quantified workload).
    feasible=0
    for i in range(160):
        rs=[ps.row([1,0,2]),ps.row([-1,0,2]),ps.row([0,1,2]),ps.row([0,-1,2])]
        for _ in range(4): rs.append(ps.row([rng.randint(-3,3) for _ in range(3)],rng.choice([False,True])))
        oracle=bounded_feasible(rs,2); result=ps.solve(list(map(ps.read,rs)),2)
        assert ('model' in result)==oracle,('differential',i,rs,result)
        feasible+=oracle
        if 'unsat' in result: assert pc.contradiction([pc.parse(r,2) for r in rs],result['unsat'],2)
        else: assert all(pc.eval_row(pc.parse(r,2),list(map(F,result['model']))) for r in rs)
        checks.append({'lane':'poly-feasibility-oracle','case':i,'feasible':oracle,'agreement':True})

    # Noncommutative critical-pair capability separation.
    a={(0,):F(1)}; b={(1,):F(1)}
    p={'generators':2,'relations':[ns.wire(ns.add(ns.mul(a,b),a,-1)),ns.wire(ns.add(ns.mul(b,a),b,-1))],
       'target':ns.wire(ns.add(ns.mul(a,a),a,-1))}
    run('nc','critical-pair-disabled',p,lambda p:ns.prove(p,complete=False),nc.check,'unknown')
    run('nc','critical-pair-enabled',p,ns.prove,nc.check,'proved')
    # Weyl normal ordering, plus an independent action on polynomials.
    weyl_rel={(1,0):F(1),(0,1):F(-1),():F(-1)}; weyl_oracles=0
    for m in range(1,7):
        for n in range(1,7):
            t={(1,)*m+(0,)*n:F(1)}
            for k in range(min(m,n)+1):
                w=(0,)*(n-k)+(1,)*(m-k)
                t[w]=t.get(w,F(0))-comb(m,k)*factorial(n)//factorial(n-k)
            t=ns.clean(t)
            p={'generators':2,'relations':[ns.wire(weyl_rel)],'target':ns.wire(t)}
            c=run('nc',f'weyl-{m}-{n}',p,ns.prove,nc.check,'proved')
            for degree in range(8): assert weyl_zero(t,degree); weyl_oracles+=1
            z=copy.deepcopy(c); z['terms'][0]['coefficient']=str(F(z['terms'][0]['coefficient'])+1)
            reject('nc',f'weyl-coefficient-{m}-{n}',p,z,nc.check)
    for i in range(40):
        qv=F(rng.randint(1,5),rng.randint(1,5)); w=tuple(rng.randrange(2) for _ in range(rng.randint(3,12)))
        inv=sum(w[j]==1 and w[k]==0 for j in range(len(w)) for k in range(j+1,len(w)))
        normal=(0,)*w.count(0)+(1,)*w.count(1)
        t=ns.add({w:F(1)},{normal:qv**inv},-1)
        p={'generators':2,'relations':[ns.wire({(1,0):F(1),(0,1):-qv})],'target':ns.wire(t)}
        c=run('nc',f'q-plane-{i:02}',p,ns.prove,nc.check,'proved')
        changed=copy.deepcopy(p); changed['target']=ns.wire(ns.add(t,{():F(1)}))
        reject('nc',f'changed-target-{i}',changed,c,nc.check)
    # Clifford: (e1+...+ed)^2=d under e_i^2=1 and anticommutation.
    for dim in range(2,7):
        rel=[]
        for i in range(dim): rel.append({(i,i):F(1),():F(-1)})
        for i in range(dim):
            for j in range(i): rel.append({(i,j):F(1),(j,i):F(1)})
        s={(i,):F(1) for i in range(dim)}; t=ns.add(ns.mul(s,s),{():F(dim)},-1)
        p={'generators':dim,'relations':list(map(ns.wire,rel)),'target':ns.wire(t)}
        run('nc',f'clifford-{dim}',p,ns.prove,nc.check,'proved')
    p={'generators':2,'relations':[],'target':ns.wire({(0,1):F(1),(1,0):F(-1)})}
    run('nc','commutativity-not-assumed',p,ns.prove,nc.check,'unknown')
    p={'generators':2,'relations':[ns.wire(weyl_rel)],'target':ns.wire({(1,0):F(1),(0,1):F(-1)})}
    run('nc','false-weyl-control',p,ns.prove,nc.check,'unknown')

    # Exact interval proofs with a positive margin.
    x=an.X; C=an.C; op=an.op; sub=an.sub
    for i in range(20):
        eps=F(rng.randint(1,9),20)
        # exp(x) >= 1/3 + epsilon on [0,1], and exp(x)+log(1+x) >= 1/2.
        e=sub(op('exp',x),C(F(1,3)+eps))
        p={'expr':e,'box':['0','1']}
        c=run('analytic',f'exp-margin-{i:02}',p,an.prove,ac.check,'interval')
        z=copy.deepcopy(c); first_leaf(z['tree'])['order']=1.5
        reject('analytic',f'bad-series-order-{i}',p,z,ac.check)
    # A true positive margin hidden by interval dependency needs subdivision.
    for i in range(12):
        eps=F(1,rng.randint(4,16))
        e=op('add',sub(x,x),C(eps)); p={'expr':e,'box':['0','1']}
        run('analytic',f'subdivision-{i:02}',p,lambda p:an.prove(p,depth=7),ac.check,'interval')
    e=op('add',sub(op('exp',x),C(1)),op('log',op('add',C(1),x)))
    p={'expr':op('add',e,C('1/8')),'box':['0','1']}
    run('analytic','exp-log-composition',p,an.prove,ac.check,'interval')
    jet_cases=[('exp',sub(sub(op('exp',x),C(1)),x),['-1','1'],2),
       ('log',sub(x,op('log',op('add',C(1),x))),['-1/2','1'],2),
       ('cos',op('add',sub(op('cos',x),C(1)),op('mul',C('1/2'),op('pow',x,2))),['-1','1'],4),
       ('sin',op('add',sub(op('sin',x),x),op('mul',C('1/6'),op('pow',x,3))),['0','1'],5)]
    for name,e,box,m in jet_cases:
        p={'expr':e,'box':box}
        run('analytic',name+'-without-jet',p,lambda p:an.prove(p,depth=3),ac.check,'unknown')
        c=run('analytic',name+'-with-jet',p,lambda p:an.prove(p,jet_order=m),ac.check,'jet')
        z=copy.deepcopy(c); z['anchor']='9'; reject('analytic',name+'-escaped-anchor',p,z,ac.check)
        z=copy.deepcopy(c); z['order']=0; reject('analytic',name+'-empty-jet',p,z,ac.check)
        wrong=copy.deepcopy(p); wrong['expr']=sub(e,C(1)); reject('analytic',name+'-wrong-target',wrong,c,ac.check)
    # Controls: false statement, unsupported analytic domain and budget exhaustion.
    for name,e,box in [('false-exp',sub(sub(op('exp',x),C(1)),op('mul',C(2),x)),['0','1']),
                        ('log-domain',op('log',x),['-1','1']),
                        ('pole-domain',['div',C(0),x],['-1','1'])]:
        run('analytic',name,{'expr':e,'box':box},lambda p:an.prove(p,depth=3),ac.check,'unknown')

    # Semantic bound and coverage corruption: the checker must recompute both.
    for r in records:
        if r['lane']=='analytic' and r['certificate']['kind']!='unknown':
            z=copy.deepcopy(r['certificate']); leaf=first_leaf(z['tree'])
            hi=F(leaf['bound'][1]); leaf['bound']=[str(hi+1),str(hi+2)]
            reject('analytic',r['name']+'-false-bound',r['problem'],z,ac.check)
            if r['certificate']['tree']['kind']=='split':
                z=copy.deepcopy(r['certificate']);z['tree']['at']=r['problem']['box'][0]
                reject('analytic',r['name']+'-coverage-hole',r['problem'],z,ac.check)

    # Canonical rational boundary controls, with one valid nonempty NC receipt.
    source=next(r for r in records if r['lane']=='nc' and r['certificate'].get('terms'))
    for value in (True,0.25,'01','2/4','nan'):
        z=copy.deepcopy(source['certificate']); z['terms'][0]['coefficient']=value
        reject('nc','noncanonical-'+str(value),source['problem'],z,nc.check)

    summary={'seed':SEED,'python':sys.version,'platform':platform.platform(),
      'evidence':'Python exact replay only; no Lean compilation or tactic comparison',
      'lanes':{},'mutation_rejections':{},
      'independent_oracles':{'poly_vertex_cases':len(checks),'poly_feasible':feasible,
          'poly_infeasible':len(checks)-feasible,'weyl_polynomial_actions':weyl_oracles},
      'witness_evaluations':witness_evaluations}
    for lane in ('poly','nc','analytic'):
        rr=[r for r in records if r['lane']==lane]; counts={}
        for r in rr:
            kind=r['certificate']['kind']; counts[kind]=counts.get(kind,0)+1
        summary['lanes'][lane]={'cases':len(rr),'outcomes':counts,
           'certificate_bytes':sum(m['certificate_bytes'] for m in metrics if m['lane']==lane)}
        summary['mutation_rejections'][lane]=sum(m['lane']==lane for m in mutations)
    for fn,data in [('certificates.json',records),('summary.json',summary),('mutations.json',mutations),('differential.json',checks)]:
        (out/fn).write_text(json.dumps(data,indent=2)+'\n')
    with (out/'measurements.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(metrics[0])); w.writeheader(); w.writerows(metrics)
    print(json.dumps(summary,indent=2))
    return summary

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=Path('reproduced-results'))
    args=parser.parse_args();experiment(args.out)
