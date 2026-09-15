#!/usr/bin/env python3
"""Replay all stored certificates with: python -S prototype/replay.py FILE.json"""
import sys,json,time
from pathlib import Path
from forge_summaries.check import verify_bundle

def no_duplicates(pairs):
    out={}
    for key,value in pairs:
        if key in out: raise ValueError('duplicate JSON key: '+key)
        out[key]=value
    return out

def load(path):
    raw=Path(path).read_bytes()
    if len(raw)>32*1024*1024: raise ValueError('file size exceeds 32 MiB')
    return json.loads(raw,object_pairs_hook=no_duplicates,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError('non-finite number')))

def main():
    if len(sys.argv)!=2: raise SystemExit('usage: python -S prototype/replay.py certificates.json')
    start=time.perf_counter(); data=load(sys.argv[1]); counts={}; failures=[]
    for entry in data['entries']:
        bundle=entry['bundle']; ok=verify_bundle(bundle)
        counts[bundle['checker']]=counts.get(bundle['checker'],0)+1
        if not ok: failures.append(entry['name'])
    print(json.dumps({'status':'PASS' if not failures else 'FAIL','entries':len(data['entries']),
                      'by_checker':counts,'failures':failures,'seconds':time.perf_counter()-start,
                      'site_packages_enabled':not sys.flags.no_site,
                      'sympy_loaded':'sympy' in sys.modules},indent=2))
    return bool(failures)
if __name__=='__main__': raise SystemExit(main())
