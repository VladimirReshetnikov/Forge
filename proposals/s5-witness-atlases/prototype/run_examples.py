from pathlib import Path
from time import perf_counter
import json,sys,traceback
from atlas.examples import examples
from atlas.producer import produce
from atlas.checker import verify,selector

ROOT=Path(__file__).resolve().parents[1]
summary=[]
for p,expected in examples():
    if len(sys.argv)>1 and p['name'] not in sys.argv[1:]:continue
    t=perf_counter();print('START',p['name'],flush=True)
    try:
        c=produce(p);t1=perf_counter();out=verify(p,c);t2=perf_counter()
        assert out['closed_value'] is expected,(p['name'],out)
        row={'name':p['name'],'expected':expected,**out,'search_seconds':t1-t,'replay_seconds':t2-t1}
        dest=ROOT/'examples'/p['name'];dest.mkdir(parents=True,exist_ok=True)
        (dest/'problem.json').write_text(json.dumps(p,indent=2)+'\n')
        (dest/'certificate.json').write_text(json.dumps(c,indent=2)+'\n')
        (dest/'strategy.json').write_text(json.dumps({'meaning':'exists witness or forall counterexample, indexed by x cell',
            'selectors':[selector(s) for s in c['stacks']]},indent=2)+'\n')
        print('OK',row,flush=True)
    except Exception as ex:
        row={'name':p['name'],'status':'FAILED','exception':repr(ex),'traceback':traceback.format_exc()}
        print(row['traceback'],flush=True)
    summary.append(row)
    (ROOT/'results'/'examples-latest.json').write_text(json.dumps(summary,indent=2)+'\n')

sys.exit(0 if summary and all(row.get("accepted",False) for row in summary) else 1)
