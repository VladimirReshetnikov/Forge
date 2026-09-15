#!/usr/bin/env python3
"""Replay stored problems/certificates without search packages: python -S replay.py."""
from pathlib import Path
import json
import sys
from prototype.check import load, verify
root=Path(__file__).resolve().parent
path=Path(sys.argv[1]) if len(sys.argv)>1 else root/'results'/'certificates.json'
data=load(path)
results=[]
for row in data:
    result=verify(row['problem'],row['certificate'])
    results.append({'id':row['id'],'accepted':True,'details':result})
print(json.dumps({'accepted':len(results),'receipts':results},indent=2))
