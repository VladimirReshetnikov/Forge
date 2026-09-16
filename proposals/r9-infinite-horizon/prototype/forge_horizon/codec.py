"""Explicit JSON transport. Fractions are tagged; targets are external to proofs."""
from __future__ import annotations
import json
from fractions import Fraction as F
from .models import PDS, Rule, Game, Chain, require

def encode(x):
    if type(x) is F: return {'rational':[x.numerator,x.denominator]}
    if isinstance(x,dict): return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(tuple,list,set,frozenset)): return [encode(v) for v in x]
    return x

def decode(x):
    if isinstance(x,dict):
        if set(x)=={'rational'}:
            pair=x['rational']; require(isinstance(pair,list) and len(pair)==2, 'rational pair')
            a,b=pair; require(type(a) is int and type(b) is int and b>0,'rational denominator')
            require(a.bit_length()<=100000 and b.bit_length()<=100000,'rational size')
            return F(a,b)
        return {k:decode(v) for k,v in x.items()}
    if isinstance(x,list): return [decode(v) for v in x]
    return x

def _unique_pairs(pairs):
    out={}
    for k,v in pairs:
        require(k not in out,'duplicate JSON key')
        out[k]=v
    return out

def loads(s: str):
    require(len(s)<=50_000_000,'JSON character budget')
    return decode(json.loads(s,object_pairs_hook=_unique_pairs))

def dumps(x) -> str:
    return json.dumps(encode(x),indent=2,sort_keys=True)+'\n'

def pack_model(m):
    if isinstance(m,PDS):
        return {'type':'pds','n':m.n,'alphabet':m.alphabet,'start':m.start,
                'stack':list(m.stack),'finals':sorted(m.finals),
                'rules':[[r.p,r.a,r.q,list(r.rhs)] for r in m.rules]}
    if isinstance(m,Game):
        return {'type':'game','owner':list(m.owner),'edges':[list(r) for r in m.edges],
                'accepting':sorted(m.accepting)}
    if isinstance(m,Chain):
        return {'type':'chain','matrix':m.matrix,'terminal':sorted(m.terminal),
                'payoff':m.payoff,'cost':m.cost,'start':m.start}
    raise TypeError(type(m))

def unpack_model(d):
    if d['type']=='pds':
        return PDS(d['n'],d['alphabet'],tuple(Rule(p,a,q,tuple(w)) for p,a,q,w in d['rules']),
                   d['start'],tuple(d['stack']),frozenset(d['finals']))
    if d['type']=='game':
        return Game(tuple(d['owner']),tuple(tuple(r) for r in d['edges']),frozenset(d['accepting']))
    if d['type']=='chain':
        return Chain(tuple(tuple(r) for r in d['matrix']),frozenset(d['terminal']),
                     tuple(d['payoff']),tuple(d['cost']),d['start'])
    raise ValueError('unknown model type')
