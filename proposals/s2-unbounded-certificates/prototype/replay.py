#!/usr/bin/env python3
"""Replay recorded certificates while actively forbidding search imports."""
import argparse, builtins, json, sys, time
from pathlib import Path
original_import=builtins.__import__
def restricted_import(name,*args,**kw):
    if name=='search' or name.startswith(('forge_unbounded.search','sympy','numpy','scipy')):
        raise ImportError('replay forbids search and optional numeric packages: '+name)
    return original_import(name,*args,**kw)
builtins.__import__=restricted_import
from forge_unbounded.verify import verify

ap=argparse.ArgumentParser()
ap.add_argument('directory',type=Path)
args=ap.parse_args()
start=time.perf_counter();counts={}
for filename,expected in [('certificates.jsonl',True),('rejections.jsonl',False)]:
    count=0
    with (args.directory/filename).open() as f:
        for line in f:
            rec=json.loads(line)
            actual=verify(rec['problem'],rec['certificate'])
            if actual != expected:
                raise SystemExit('replay disagreement: '+rec['name'])
            count+=1
    counts[filename]=count
assert 'forge_unbounded.search' not in sys.modules
print(json.dumps({'status':'PASSED','counts':counts,'seconds':time.perf_counter()-start,
                  'search_imported':False,'site_packages_enabled':not sys.flags.no_site},indent=2))
