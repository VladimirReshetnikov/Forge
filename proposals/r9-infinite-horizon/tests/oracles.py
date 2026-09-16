"""Reference computations. None imports a search engine or replay checker."""
from __future__ import annotations
from collections import deque
from fractions import Fraction as F
from itertools import product
from forge_horizon.models import PDS, Game, Chain


def pds_bfs(p: PDS, max_height: int, target=None):
    """Exact on non-growing inputs; otherwise reports whether truncation occurred."""
    if target is None: target=lambda q,w:q in p.finals and not w
    start=(p.start,p.stack); seen={start}; todo=deque([start]); truncated=False
    while todo:
        q,w=todo.popleft()
        if target(q,w): return True,not truncated,len(seen)
        if not w: continue
        for r in p.rules:
            if (r.p,r.a)!=(q,w[0]): continue
            t=(r.q,r.rhs+w[1:])
            if len(t[1])>max_height: truncated=True; continue
            if t not in seen: seen.add(t); todo.append(t)
    return False,not truncated,len(seen)


def expanded_pds_trace(p: PDS, cert: dict, limit: int=20000):
    q=p.start; stack=p.stack; agenda=list(reversed(cert['chain'])); steps=0
    while agenda:
        i=agenda.pop(); node=cert['nodes'][i]; r=p.rules[node['rule']]
        assert stack and (q,stack[0])==(r.p,r.a)
        q=r.q; stack=r.rhs+stack[1:]; steps+=1
        if steps>limit: return None
        agenda.extend(reversed(node['children']))
    assert not stack and q in p.finals
    return steps


def _reach(edges,allowed=None):
    n=len(edges)
    if allowed is None: allowed=set(range(n))
    r=[[False]*n for _ in range(n)]
    for v in allowed:
        for w in edges[v]:
            if w in allowed:r[v][w]=True
    for k in allowed:
        for i in allowed:
            if r[i][k]:
                for j in allowed:r[i][j]=r[i][j] or r[k][j]
    return r


def game_oracle(g: Game):
    """Enumerate both players' positional policies, inspect their cycle graphs."""
    winning=set(); losing=set()
    for player,result in ((0,winning),(1,losing)):
        controlled=[v for v in range(g.n) if g.owner[v]==player]
        for choices in product(*(g.edges[v] for v in controlled)):
            fixed=dict(zip(controlled,choices))
            edges=[(fixed[v],) if v in fixed else g.edges[v] for v in range(g.n)]
            full=_reach(edges)
            if player==0:
                restricted=_reach(edges,set(range(g.n))-g.accepting)
                cycles={v for v in range(g.n) if restricted[v][v]}
            else:
                cycles={v for v in g.accepting if full[v][v]}
            for s in range(g.n):
                if not any(s==v or full[s][v] for v in cycles):result.add(s)
    assert winning.isdisjoint(losing) and winning|losing==set(range(g.n))
    return winning,losing


def determinant(a):
    """Laplace expansion, deliberately not Gaussian elimination."""
    if not a:return F(1)
    if len(a)==1:return a[0][0]
    ans=F(0)
    for j,x in enumerate(a[0]):
        if x:
            minor=[row[:j]+row[j+1:] for row in a[1:]]
            ans+=(-1 if j%2 else 1)*x*determinant(minor)
    return ans


def chain_cramer(c: Chain):
    transient=[s for s in range(c.n) if s not in c.terminal]
    a=[[F(int(s==t))-c.matrix[s][t] for t in transient] for s in transient]
    denom=determinant(a); assert denom
    bs=[[F(1) for s in transient],[c.cost[s] for s in transient],
        [sum((c.matrix[s][t]*c.payoff[t] for t in c.terminal),F(0)) for s in transient]]
    answers=[]
    for b in bs:
        x={}
        for j,s in enumerate(transient):
            m=[list(row) for row in a]
            for i in range(len(m)):m[i][j]=b[i]
            x[s]=determinant(m)/denom
        answers.append(x)
    return answers


def chain_acyclic(c: Chain):
    h=[F(0)]*c.n; v=list(h); u=list(c.payoff)
    for s in reversed(range(c.n)):
        if s in c.terminal:continue
        assert all(p==0 for p in c.matrix[s][:s+1])
        h[s]=1+sum((p*h[t] for t,p in enumerate(c.matrix[s])),F(0))
        v[s]=c.cost[s]+sum((p*v[t] for t,p in enumerate(c.matrix[s])),F(0))
        u[s]=sum((p*u[t] for t,p in enumerate(c.matrix[s])),F(0))
    return h,v,u


def chain_as_oracle(c: Chain):
    """Enumerate all nonterminal closed subsets, rather than compute SCCs."""
    edges=[[t for t,p in enumerate(row) if p>0] for row in c.matrix]
    r=_reach(edges)
    reachable={c.start}|{t for t in range(c.n) if r[c.start][t]}
    candidates=sorted(reachable-c.terminal)
    for mask in range(1,1<<len(candidates)):
        subset={v for i,v in enumerate(candidates) if mask&(1<<i)}
        if all(w in subset for v in subset for w in edges[v]):return False
    return True
