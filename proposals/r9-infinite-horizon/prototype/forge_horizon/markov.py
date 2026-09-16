"""Exact finite-chain synthesis; replay never imports this module."""
from __future__ import annotations
from collections import deque
from fractions import Fraction as F
from .models import Chain, require


def _solve_many(a: list[list[F]], b: list[list[F]]) -> list[list[F]]:
    """Gauss--Jordan search with several right-hand sides; exact fractions."""
    n=len(a)
    if not n:
        return []
    aug=[list(a[i])+list(b[i]) for i in range(n)]
    for col in range(n):
        pivot=next((r for r in range(col,n) if aug[r][col]),None)
        require(pivot is not None, 'singular transient matrix')
        aug[col],aug[pivot]=aug[pivot],aug[col]
        scale=aug[col][col]
        aug[col]=[x/scale for x in aug[col]]
        for r in range(n):
            if r!=col and aug[r][col]:
                scale=aug[r][col]
                aug[r]=[x-scale*y for x,y in zip(aug[r],aug[col])]
    return [row[n:] for row in aug]


def _components(vertices: set[int], edges: list[list[int]]) -> list[set[int]]:
    """Iterative Kosaraju (no Python recursion-limit dependence)."""
    seen=set(); order=[]
    for root in sorted(vertices):
        if root in seen: continue
        todo=[(root,False)]
        while todo:
            v,finish=todo.pop()
            if finish:
                order.append(v); continue
            if v in seen: continue
            seen.add(v); todo.append((v,True))
            for w in reversed(edges[v]):
                if w in vertices and w not in seen: todo.append((w,False))
    reverse=[[] for _ in edges]
    for v in vertices:
        for w in edges[v]:
            if w in vertices: reverse[w].append(v)
    seen=set(); parts=[]
    for root in reversed(order):
        if root in seen: continue
        part=set(); todo=[root]; seen.add(root)
        while todo:
            v=todo.pop(); part.add(v)
            for w in reverse[v]:
                if w not in seen: seen.add(w); todo.append(w)
        parts.append(part)
    return parts


def solve(c: Chain) -> dict:
    c.validate(); edges=[[t for t,p in enumerate(row) if p>0] for row in c.matrix]
    parent={c.start:None}; todo=deque([c.start])
    while todo:
        v=todo.popleft()
        for w in edges[v]:
            if w not in parent: parent[w]=v; todo.append(w)
    support=set(parent)
    for part in _components(support,edges):
        if not(part & c.terminal) and all(w in part for v in part for w in edges[v]):
            q=min(part); path=[]
            while q is not None: path.append(q); q=parent[q]
            return {'kind':'mc_trap','closed':sorted(part),'path':list(reversed(path))}
    transient=sorted(support-c.terminal)
    a=[[F(int(s==t))-c.matrix[s][t] for t in transient] for s in transient]
    b=[[F(1),c.cost[s],sum((c.matrix[s][t]*c.payoff[t] for t in c.terminal),F(0))]
       for s in transient]
    solution=_solve_many(a,b)
    h=[None]*c.n; v=[None]*c.n; u=[None]*c.n
    for t in support & c.terminal:
        h[t]=v[t]=F(0); u[t]=c.payoff[t]
    for s,row in zip(transient,solution):
        h[s],v[s],u[s]=row
    return {'kind':'mc_absorb','support':sorted(support),'time':h,'cost':v,'value':u}
