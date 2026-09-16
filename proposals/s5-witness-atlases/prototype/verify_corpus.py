"""Usage: python -S verify_corpus.py [corpus directory]. No search dependency."""
from pathlib import Path
import json,sys,time,platform
from atlas.checker import verify
from atlas.io import load
from atlas.exact import LimitExceeded

root=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'examples'
rows=[]
for path in sorted(root.glob('*/problem.json')):
    t=time.perf_counter()
    try:
        row={'name':path.parent.name,**verify(load(path),load(path.with_name('certificate.json')))}
    except LimitExceeded as ex:
        row={'name':path.parent.name,'status':'UNKNOWN','reason':str(ex)}
    except Exception as ex:
        row={'name':path.parent.name,'status':'REJECTED','reason':str(ex)}
    row['seconds']=time.perf_counter()-t;rows.append(row)
print(json.dumps({'python':sys.version,'platform':platform.platform(),'site_disabled':bool(sys.flags.no_site),
                  'sympy_loaded':any(m=='sympy' or m.startswith('sympy.') for m in sys.modules),
                  'accepted':sum(r.get('accepted',False) for r in rows),'records':len(rows),'results':rows},indent=2))
sys.exit(0 if rows and all(r.get('accepted',False) for r in rows) else 1)
