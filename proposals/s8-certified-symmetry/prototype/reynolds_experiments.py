"""Separate supplementary run, with full-group averaging as a small oracle."""
import sys
if not __debug__:
    raise RuntimeError("Regression and replay scripts require assertions enabled; do not use -O")
import argparse, copy, json, random
from fractions import Fraction
from pathlib import Path
from forge_symmetry.producer import named_problem,build_chain,enumerate_bfs
from forge_symmetry.checker import verify_chain,InvalidCertificate,load_json
from forge_symmetry.reynolds_producer import project_certificate
from forge_symmetry.reynolds_checker import verify_projection

parser=argparse.ArgumentParser(); parser.add_argument('--output',default='../reproduced-reynolds')
args=parser.parse_args(); out=Path(args.output);out.mkdir(parents=True,exist_ok=False)
rng=random.Random(20260915); bundles=[]
for family in ['S','A','C','D','trivial']:
 for n in range(2,7):
  problem=named_problem(family,n); chaincert=build_chain(problem).export()
  checked=verify_chain(problem,chaincert)
  coefficients={}
  for _ in range(5):
   exponent=tuple(rng.randrange(3) for _ in range(n))
   coefficients[exponent]=Fraction(rng.choice([-3,-2,-1,1,2,3]),rng.choice([1,2,3]))
  terms=[[list(e),q.numerator,q.denominator] for e,q in sorted(coefficients.items())]
  cert=project_certificate(problem,terms); result=verify_projection(checked,terms,cert)
  oracle={}; group=enumerate_bfs(problem)
  for g in group:
   for e,q in coefficients.items():
    renamed=tuple(e[g.index(j)] for j in range(n))
    oracle[renamed]=oracle.get(renamed,Fraction())+q/len(group)
  expected=[[list(e),q.numerator,q.denominator] for e,q in sorted(oracle.items()) if q]
  assert result['output']==expected
  again=project_certificate(problem,expected)
  assert verify_projection(checked,expected,again)['output']==expected
  bundles.append({'case':family+str(n),'problem':problem,'chain':chaincert,'terms':terms,'certificate':cert})
# A large-group orbit computation: 40!*terms not enumerated.
problem=named_problem('S',40); chaincert=build_chain(problem).export(); checked=verify_chain(problem,chaincert)
terms=[[[2,1]+[0]*38,1,1]]
cert=project_certificate(problem,terms); result=verify_projection(checked,terms,cert)
assert result['monomial_count']==40*39 and all(row[1:]==[1,1560] for row in result['output'])
bundles.append({'case':'S40-mixed-cubic','problem':problem,'chain':chaincert,'terms':terms,'certificate':cert})
# Controls independent of success counts.
base=bundles[0]; controls=[]
for name,edit in [('missing-support',lambda c:c['orbits'].clear()),
                  ('wrong-average',lambda c:c['output'][0].__setitem__(1,987)),
                  ('bad-edge',lambda c:next(t for t in c['orbits'] if len(t)>1)[1].__setitem__(2,999)),
                  ('Boolean-exponent',lambda c:c['orbits'][0][0][0].__setitem__(0,True))]:
 c=copy.deepcopy(base['certificate']);edit(c)
 try: verify_projection(verify_chain(base['problem'],base['chain']),base['terms'],c)
 except InvalidCertificate as e: controls.append({'case':name,'result':'rejected','reason':str(e)})
 else: raise AssertionError('corruption accepted: '+name)
(out/'bundles.json').write_text(json.dumps(bundles,separators=(',',':'))+'\n')
summary={'status':'ALL_ASSERTIONS_PASSED','seed':20260915,'small_full_group_average_comparisons':25,
         'idempotence_checks':25,'large_projection_instances':1,'large_monomial_orbit_size':1560,
         'malformed_rejections':controls, 'lean_status':'NOT_RUN'}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n'); print(json.dumps(summary,indent=2))
