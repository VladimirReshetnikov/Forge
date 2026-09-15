#!/usr/bin/env python3
"""Replay all stored evidence with stdlib alone: python -S prototype/replay_corpus.py."""
import argparse,json,sys,time
from pathlib import Path
from verify_stdlib import read_json,check_certificate,check_counterexample

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]/'results'/'experiment')
    ap.add_argument('--output',type=Path)
    a=ap.parse_args();receipts=[];start=time.perf_counter()
    for path in sorted((a.root/'evidence').glob('*.json')):
        case=path.name.rsplit('.',2)[0]
        problem=read_json(a.root/'problems'/f'{case}.json');ev=read_json(path)
        fn=check_counterexample if ev['schema']=='forge-counterexample-v1' else check_certificate
        receipts.append(dict(file=path.name,**fn(problem,ev)))
    result=dict(accepted=len(receipts),receipts=receipts,site_disabled=bool(sys.flags.no_site),
                search_imported='search' in sys.modules,sympy_imported='sympy' in sys.modules,
                elapsed_seconds=time.perf_counter()-start)
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(text)
    print(json.dumps({k:v for k,v in result.items() if k!='receipts'},sort_keys=True))

if __name__=='__main__':main()
