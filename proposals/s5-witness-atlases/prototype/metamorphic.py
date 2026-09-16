"""Invertible affine changes preserve closed quantified truth; independent fixture labels."""
from pathlib import Path
import json,time
from atlas.examples import examples
from atlas.producer import produce,problem,symbolic,x,y
from atlas import polynomial as P
from atlas.checker import verify
ROOT=Path(__file__).resolve().parents[1]
transforms=[(1,1,1,-1),(-1,0,1,2),(2,-1,-1,1),(-2,3,2,-3)]
rows=[];t=time.perf_counter()
for p,expected in examples():
    if expected is None:continue
    original=[symbolic(P.decode(v)) for v in p['polynomials']]
    for k,(a,b,c,d) in enumerate(transforms):
        polys=[f.subs({x:a*x+b,y:c*y+d},simultaneous=True).expand() for f in original]
        p2=problem(p['name']+'_affine_'+str(k),polys,p['formula'],p['outer'],p['inner'])
        start=time.perf_counter();cert=produce(p2);mid=time.perf_counter();r=verify(p2,cert)
        assert r['closed_value'] is expected
        dst=ROOT/'metamorphic-corpus'/p2['name'];dst.mkdir(parents=True,exist_ok=True)
        for filename,obj in [('problem.json',p2),('certificate.json',cert)]:
            (dst/filename).write_text(json.dumps(obj,indent=2)+'\n')
        rows.append({'name':p2['name'],'original':p['name'],'transform':[a,b,c,d],
                     'expected':expected,**r,'search_seconds':mid-start,'replay_seconds':time.perf_counter()-mid})
out={'cases':len(rows),'agreements':len(rows),'seconds':time.perf_counter()-t,'records':rows}
(ROOT/'results'/'metamorphic.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='records'})
