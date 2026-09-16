"""Finite-carrier/exhaustive-state differential oracles. No search-module imports.

Counter oracles require token-conserving rules and fixed initial markings, so
queue exhaustion is a complete finite graph search, not a guessed cutoff.
The equality oracle explores ALL words over its finite carrier via state BFS.
Carrier k_total + c + 1 is justified by the article's explicit cutoff theorem.
These oracles share the checker interpreter, a disclosed residual dependency.
"""
from __future__ import annotations
from collections import deque
import checker


def finite_vass(problem: dict) -> dict:
    assert all(not f['rays'] for f in problem['initials'])
    assert all(sum(e['consume']) == sum(e['produce']) for e in problem['transitions'])
    starts=[(f['control'],tuple(f['base'])) for f in problem['initials']]
    todo=deque(starts);seen=set(starts)
    while todo:
        q,x=todo.popleft()
        if any(q==b['control'] and all(x[i]>=b['vector'][i] for i in range(len(x))) for b in problem['bad']):
            return {'safe':False,'states':len(seen)}
        for e in problem['transitions']:
            if e['src']!=q or any(x[i]<e['consume'][i] for i in range(len(x))):continue
            y=tuple(x[i]+e['produce'][i]-e['consume'][i] for i in range(len(x)))
            nxt=(e['dst'],y)
            if nxt not in seen: seen.add(nxt);todo.append(nxt)
    return {'safe':True,'states':len(seen)}


def finite_nominal(left: dict, right: dict, alphabet_size: int | None = None) -> dict:
    if alphabet_size is None:
        alphabet_size=left['registers']+right['registers']+left['constants']+1
    assert alphabet_size>=left['constants'] and alphabet_size>0
    start=((left['initial_control'],tuple(left['initial_registers'])),
           (right['initial_control'],tuple(right['initial_registers'])))
    todo=deque([(start,0)]);seen={start}
    while todo:
        (sa,sb),depth=todo.popleft()
        for tag in left['tags']:
            for atom in range(alphabet_size):
                oa,na=checker.execute(left,sa,tag,atom)
                ob,nb=checker.execute(right,sb,tag,atom)
                if oa!=ob:return {'equivalent':False,'states':len(seen),'shortest_length':depth+1,
                                  'alphabet_size':alphabet_size}
                nxt=(na,nb)
                if nxt not in seen:seen.add(nxt);todo.append((nxt,depth+1))
    return {'equivalent':True,'states':len(seen),'shortest_length':None,'alphabet_size':alphabet_size}


def finite_mixed(model: dict) -> dict:
    assert all(not f['rays'] for f in model['initials'])
    assert all(sum(r['consume']) == sum(r['produce']) for r in model['rules'])
    alphabet_size=model['registers']+model['constants']+1
    starts=[(model['initial_control'],tuple(model['initial_registers']),tuple(f['base'])) for f in model['initials']]
    todo=deque(starts);seen=set(starts)
    while todo:
        q,regs,counters=todo.popleft()
        if any(b['control']==q and checker.eval_condition(b['guard'],regs,0)
               and all(x>=y for x,y in zip(counters,b['vector'])) for b in model['bad']):
            return {'safe':False,'states':len(seen),'alphabet_size':alphabet_size}
        for r in model['rules']:
            if r['src']!=q or any(x<y for x,y in zip(counters,r['consume'])):continue
            for atom in range(alphabet_size):
                if not checker.eval_condition(r['guard'],regs,atom):continue
                newregs=tuple(checker.eval_selector(e,regs,atom) for e in r['update'])
                newcounts=tuple(c+r['produce'][i]-r['consume'][i] for i,c in enumerate(counters))
                nxt=(r['dst'],newregs,newcounts)
                if nxt not in seen:seen.add(nxt);todo.append(nxt)
    return {'safe':True,'states':len(seen),'alphabet_size':alphabet_size}
