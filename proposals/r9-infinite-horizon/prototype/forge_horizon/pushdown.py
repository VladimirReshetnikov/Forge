"""Indexed least-fixed-point search for pushdown pop summaries."""
from __future__ import annotations
from collections import defaultdict, deque
from .models import PDS, Rule, require, natural


def solve(p: PDS) -> dict:
    p.validate()
    unary=defaultdict(list); first=defaultdict(list); second=defaultdict(list)
    nodes=[]; ids={}; outgoing=defaultdict(dict); todo=deque()
    stats={'new_summaries':0,'join_attempts':0}
    def add(tr, rid, children):
        if tr in ids:
            return
        i=len(nodes); ids[tr]=i
        nodes.append({'triple':list(tr),'rule':rid,'children':list(children)})
        outgoing[tr[:2]][tr[2]]=i; todo.append(tr)
        stats['new_summaries']+=1
    for rid,r in enumerate(p.rules):
        if not r.rhs:
            add((r.p,r.a,r.q),rid,())
        elif len(r.rhs)==1:
            unary[r.q,r.rhs[0]].append((rid,r))
        else:
            b,c=r.rhs
            first[r.q,b].append((rid,r))
            second[c].append((rid,r))
    while todo:
        q,b,m=todo.popleft(); child=ids[q,b,m]
        for rid,r in unary[q,b]:
            add((r.p,r.a,m),rid,(child,))
        for rid,r in first[q,b]:
            for t,right in list(outgoing[m,r.rhs[1]].items()):
                stats['join_attempts']+=1
                add((r.p,r.a,t),rid,(child,right))
        # New summary is the second child; its start q is the middle control.
        for rid,r in second[b]:
            left=ids.get((r.q,r.rhs[0],q))
            if left is not None:
                stats['join_attempts']+=1
                add((r.p,r.a,m),rid,(left,child))
    paths={p.start:[]}
    for a in p.stack:
        nxt={}
        for q,path in sorted(paths.items()):
            for t,i in sorted(outgoing[q,a].items()):
                if t not in nxt:
                    nxt[t]=path+[i]
        paths=nxt
    candidates=sorted(set(paths)&p.finals)
    if not candidates:
        return {'kind':'pds_exclude','relation':[list(t) for t in sorted(ids)],'stats':stats}
    roots=paths[candidates[0]]
    used=set(); agenda=list(roots)
    while agenda:
        i=agenda.pop()
        if i not in used:
            used.add(i); agenda.extend(nodes[i]['children'])
    order=sorted(used); remap={old:i for i,old in enumerate(order)}
    sliced=[{'triple':nodes[i]['triple'],'rule':nodes[i]['rule'],
             'children':[remap[j] for j in nodes[i]['children']]} for i in order]
    return {'kind':'pds_reach','nodes':sliced,'chain':[remap[i] for i in roots], 'stats':stats}


def compile_regular_target(p: PDS, delta: tuple[tuple[int,...],...],
                           initial: tuple[int,...], accepting: frozenset[int]) -> PDS:
    """Reduce reachability of a control-indexed regular stack target to empty stack.

Top-of-stack is the FIRST symbol. The DFA reads the stack from top to bottom.
The input p.finals is deliberately unused: the target is supplied by this DFA.
A fresh bottom marker makes the monitor switch possible even on an empty stack.
This compiler is tested but NOT formally verified; its source theorem is pending.
"""
    p.validate(); k=len(delta)
    require(k>0 and len(initial)==p.n, 'DFA dimensions')
    require(all(natural(x,k) for x in initial), 'DFA starts')
    require(all(natural(x,k) for x in accepting), 'DFA accepting')
    for row in delta:
        require(len(row)==p.alphabet and all(natural(x,k) for x in row), 'total DFA')
    bottom=p.alphabet; done=p.n+k
    rules=list(p.rules)
    # Switch once, preserving the unread suffix. Monitor cannot return to source.
    for q in range(p.n):
        for a in range(p.alphabet+1):
            rules.append(Rule(q,a,p.n+initial[q],(a,)))
    for q,row in enumerate(delta):
        for a,t in enumerate(row):
            rules.append(Rule(p.n+q,a,p.n+t,()))
        if q in accepting:
            rules.append(Rule(p.n+q,bottom,done,()))
    return PDS(done+1,p.alphabet+1,tuple(rules),p.start,p.stack+(bottom,),frozenset({done}))
