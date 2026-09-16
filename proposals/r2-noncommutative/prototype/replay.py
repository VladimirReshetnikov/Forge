#!/usr/bin/env python3
"""Replay recorded evidence with producer imports actively forbidden."""
import argparse, importlib.abc, json, sys
from pathlib import Path
class NoProducer(importlib.abc.MetaPathFinder):
    def find_spec(self,fullname,path=None,target=None):
        if fullname in ('ncforge.algebra','ncforge.search','experiments'):
            raise ImportError('producer access is forbidden during replay: '+fullname)
sys.meta_path.insert(0,NoProducer())
from ncforge.checker import load_json,verify
ap=argparse.ArgumentParser(); ap.add_argument('file',nargs='?',type=Path,default=Path('../results/certificates.json'))
args=ap.parse_args(); entries=load_json(args.file)
failures=[]
for entry in entries:
    ans=verify(entry['problem'],entry['certificate'])
    if not ans['accepted']: failures.append({'name':entry['name'],'result':ans})
print(json.dumps({'objects_replayed':len(entries),'failures':failures,
                  'producer_imports_blocked':True,'site_packages_disabled':bool(sys.flags.no_site)},indent=2))
sys.exit(bool(failures))
