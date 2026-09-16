"""Standalone supplementary replay: python -S verify_reynolds.py PATH/bundles.json"""
import sys
if not __debug__:
    raise RuntimeError("Regression and replay scripts require assertions enabled; do not use -O")
import json,sys
from forge_symmetry.checker import load_json,verify_chain,require
from forge_symmetry.reynolds_checker import verify_projection
bundles=load_json(sys.argv[1]);require(type(bundles)is list and len(bundles)==26,'expected full 26-case corpus')
expected={f'{f}{n}' for f in ['S','A','C','D','trivial'] for n in range(2,7)}|{'S40-mixed-cubic'}
require({b['case'] for b in bundles}==expected,'unexpected or duplicated Reynolds case identities')
for bundle in bundles:
 chain=verify_chain(bundle['problem'],bundle['chain'])
 verify_projection(chain,bundle['terms'],bundle['certificate'])
assert not any(name.endswith('producer') for name in sys.modules)
print(json.dumps({'status':'REPLAY_PASSED','bundles':len(bundles),
 'site_packages_disabled':bool(sys.flags.no_site),'producer_imported':False},indent=2))
