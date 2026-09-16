#!/usr/bin/env python3
"""Automatic rediscovery of the same four jet goals; do not pool case counts."""
import argparse,json
from pathlib import Path
from forge_delta.analytic_search import auto_prove
from forge_delta.analytic_check import check

def main(source,out):
    results=[]
    for r in json.loads(source.read_text()):
        if r['lane']=='analytic' and r['name'].endswith('-with-jet'):
            c=auto_prove(r['problem']); assert check(r['problem'],c),(r['name'],c)
            results.append({'name':r['name'],'problem':r['problem'],'certificate':c})
    out.write_text(json.dumps({'scope':'same four goals, automatic proposal profile; not extra independent cases','results':results},indent=2)+'\n')
    print([(r['name'],r['certificate'].get('order'),r['certificate'].get('discovery')) for r in results])
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=Path('../results/certificates.json'));p.add_argument('--out',type=Path,default=Path('jet-discovery.json'));a=p.parse_args();main(a.source,a.out)
