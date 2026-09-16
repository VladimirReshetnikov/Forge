"""Check selected root ordinals/sectors at rational x other than stored samples.
This uses the replay arithmetic, not an independent arithmetic implementation.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,time
from atlas.io import load
from atlas import exact as E, polynomial as P
from atlas.checker import fiber_product,evaluate_formula,selector,verify
ROOT=Path(__file__).resolve().parents[1]
probes=[Q(-5),Q(-3),Q(-2),Q(-1),Q(-1,2),Q(-1,4),Q(0),Q(1,4),Q(1,2),Q(1),Q(3,2),Q(2),Q(3),Q(5)]
rows=[];t=time.perf_counter()
for path in sorted((ROOT/'examples').glob('*/problem.json')):
    p,c=load(path),load(path.with_name('certificate.json'));verify(p,c)
    base=E.verify_root_cover(P.decode_dense(c['projection']),c['base_roots'])
    factors=[P.decode(v) for v in c['factors']]
    for q in probes:
        i=2*len(base)
        for k,r in enumerate(base):
            s=r.sign_at((-q,Q(1)))
            if s==0:i=2*k+1;break
            if s>0:i=2*k;break
        stack=c['stacks'][i];j=stack['selection']
        if j is None:continue
        fp=fiber_product(factors,q);roots=E.isolate_roots(fp)
        assert len(roots)==len(stack['y_roots'])
        polys=[E.coefficient_at_x(P.decode(v),q) for v in p['polynomials']]
        if j%2:
            signs=[roots[j//2].sign_at(v) for v in polys]
        else:
            yy=E.sector_samples(roots)[j//2]
            signs=[E.sign(E.evaluate(v,yy)) for v in polys]
        actual=evaluate_formula(p['formula'],signs)
        assert actual is (p['inner']=='exists'),(p['name'],q,j)
        rows.append({'name':p['name'],'x':str(q),'base_cell':i,'selected_y_cell':j,
                     'selector':selector(stack),'required_truth':actual})
out={'probes':len(rows),'accepted':len(rows),'seconds':time.perf_counter()-t,'records':rows}
(ROOT/'results'/'strategy-probes.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='records'})
