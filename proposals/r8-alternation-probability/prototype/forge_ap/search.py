"""Untrusted exact proposers: Zielonka, max-flow, policy iteration, simulation.

The check module is never imported. All certificates are plain data. A bounded
or interrupted search is not negative evidence; exceptions are diagnostic.
"""
from __future__ import annotations
from collections import deque
from fractions import Fraction as Q
from .models import Arena, Transport, MDP, Simulation, encq, encdist


def solve_parity(p: Arena, stats: dict | None = None) -> dict:
    stats = stats if stats is not None else {}
    stats["recursive_calls"] = 0
    def attract(player, target, universe):
        a = set(target); strategy = {}
        changed = True
        while changed:
            changed = False
            for v in sorted(universe - a):
                successors = [w for w in p.edges[v] if w in universe]
                if not successors: raise RuntimeError("non-total recursive subgame")
                good = [w for w in successors if w in a]
                if p.owner[v] == player and good:
                    a.add(v); strategy[v] = good[0]; changed = True
                elif p.owner[v] != player and len(good) == len(successors):
                    a.add(v); changed = True
        return a, strategy
    def zielonka(u):
        stats["recursive_calls"] += 1
        if not u: return [set(), set()], [{}, {}]
        priority = max(p.priority[v] for v in u); player = priority % 2; other = 1-player
        target = {v for v in u if p.priority[v] == priority}
        a, astrategy = attract(player, target, u)
        w, strategy = zielonka(u - a)
        if not w[other]:
            w[player] |= a
            strategy[player].update(astrategy)
            for v in sorted(target):
                if p.owner[v] == player:
                    strategy[player][v] = next(t for t in p.edges[v] if t in u)
            return w, strategy
        b, bstrategy = attract(other, w[other], u)
        ww, ss = zielonka(u-b)
        ww[other] |= b
        ss[other].update(bstrategy)
        ss[other].update(strategy[other])
        return ww, ss
    w, strategy = zielonka(set(range(p.n)))
    certificates = []
    for player in (0, 1):
        policy = [-1] * p.n
        edges = []
        for v in sorted(w[player]):
            if p.owner[v] == player:
                policy[v] = strategy[player][v]; edges.append((v, policy[v]))
            else: edges.extend((v, t) for t in p.edges[v])
        ranks = []
        for priority in sorted({p.priority[v] for v in w[player]
                                if p.priority[v] % 2 != player}):
            r = [0]*p.n
            threshold_edges = [(v,t) for v,t in edges
                               if max(p.priority[v], p.priority[t]) <= priority]
            # Difference-constraint relaxation, not the final local checker.
            for _ in range(p.n):
                rr = r.copy()
                for v,t in threshold_edges:
                    rr[v] = max(rr[v], r[t] + int(p.priority[v] == priority))
                if rr == r: break
                r = rr
            if any(r[v] < r[t] + int(p.priority[v] == priority) for v,t in threshold_edges):
                raise RuntimeError("proposed strategy has an unfavorable cycle")
            ranks.append({"priority": priority, "values": r})
        certificates.append({"player": player, "vertices": sorted(w[player]),
                             "strategy": policy, "ranks": ranks})
    return {"regions": certificates}


def solve_transport(p: Transport, stats: dict | None = None) -> dict:
    stats = stats if stats is not None else {}
    m, n = len(p.mu), len(p.nu); source = m+n; sink = source+1; count=sink+1
    cap = [[Q(0) for _ in range(count)] for _ in range(count)]
    for i in range(m): cap[source][i] = p.mu[i]
    for j in range(n): cap[m+j][sink] = p.nu[j]
    for i in range(m):
        for j in range(n):
            if p.relation[i][j]: cap[i][m+j] = Q(1)
    residual = [row.copy() for row in cap]
    stats["augmentations"] = 0
    while True:
        parent = [-1]*count; parent[source]=source; queue=deque([source])
        while queue and parent[sink] < 0:
            v=queue.popleft()
            for t in range(count):
                if residual[v][t] > 0 and parent[t] < 0:
                    parent[t]=v; queue.append(t)
        if parent[sink] < 0: break
        delta=Q(1); t=sink
        while t != source:
            v=parent[t]; delta=min(delta,residual[v][t]); t=v
        t=sink
        while t != source:
            v=parent[t]; residual[v][t]-=delta; residual[t][v]+=delta; t=v
        stats["augmentations"] += 1
    supported = [[cap[i][m+j]-residual[i][m+j] for j in range(n)] for i in range(m)]
    left = [p.mu[i]-sum(supported[i]) for i in range(m)]
    right = [p.nu[j]-sum(supported[i][j] for i in range(m)) for j in range(n)]
    deficit = sum(left)
    joint = [row.copy() for row in supported]
    if deficit:
        for i in range(m):
            for j in range(n): joint[i][j] += left[i]*right[j]/deficit
    reachable={source}; queue=deque([source])
    while queue:
        v=queue.popleft()
        for t in range(count):
            if residual[v][t]>0 and t not in reachable:
                reachable.add(t);queue.append(t)
    a = [i for i in range(m) if i in reachable] if deficit else []
    return {"joint": [encdist(row) for row in joint], "bad_mass": encq(deficit),
            "hall_subset": a}


def linear_solve(matrix, rhs):
    """Exact Gauss-Jordan elimination. The testing oracle uses Cramer's rule."""
    n=len(rhs)
    a=[list(map(Q,matrix[i]))+[Q(rhs[i])] for i in range(n)]
    for col in range(n):
        pivot=next((row for row in range(col,n) if a[row][col]),None)
        if pivot is None: raise RuntimeError("singular policy matrix")
        a[col],a[pivot]=a[pivot],a[col]
        d=a[col][col];a[col]=[x/d for x in a[col]]
        for row in range(n):
            if row != col and a[row][col]:
                d=a[row][col]; a[row]=[x-d*y for x,y in zip(a[row],a[col])]
    return [a[i][-1] for i in range(n)]


def solve_mdp(p: MDP, stats: dict | None = None) -> dict:
    stats = stats if stats is not None else {}
    reach={p.start}; parent={}; queue=deque([p.start])
    while queue:
        s=queue.popleft()
        for a,d in enumerate(p.actions[s]):
            for t,mass in enumerate(d):
                if mass>0 and t not in reach:
                    reach.add(t);parent[t]=(s,a);queue.append(t)
    terminal=set(p.terminal); nonterminal=reach-terminal; trap=set(nonterminal)
    stats["trap_iterations"]=0
    while True:
        smaller={s for s in trap if any(all(d[t]==0 or t in trap for t in range(p.n))
                                       for d in p.actions[s])}
        stats["trap_iterations"]+=1
        if smaller==trap:break
        trap=smaller
    if trap:
        policy=[-1]*p.n
        for s in sorted(trap):
            policy[s]=next(a for a,d in enumerate(p.actions[s])
                           if all(d[t]==0 or t in trap for t in range(p.n)))
        target=min(trap); cur=target; path=[]; probability=Q(1)
        while cur!=p.start:
            prev,a=parent[cur];path.append([a,cur]);probability*=p.actions[prev][a][cur];cur=prev
        path.reverse()
        return {"outcome":"nontermination","trap":sorted(trap),"policy":policy,
                "path":path,"probability_lower":encq(probability)}
    states=sorted(nonterminal); policy=[-1]*p.n
    for s in states:policy[s]=0
    stats["policy_evaluations"]=0
    visited=set()
    while True:
        key=tuple(policy)
        if key in visited:raise RuntimeError("policy iteration repeated a policy")
        visited.add(key)
        q=[[Q(int(s==t))-p.actions[s][policy[s]][t] for t in states] for s in states]
        solution=linear_solve(q,[Q(1)]*len(states)); vals=[Q(0)]*p.n
        for s,v in zip(states,solution):vals[s]=v
        stats["policy_evaluations"]+=1
        changed=False
        for s in states:
            alternatives=[1+sum((d[t]*vals[t] for t in range(p.n)),Q(0)) for d in p.actions[s]]
            best=max(alternatives)
            if best>vals[s]:policy[s]=alternatives.index(best);changed=True
        if not changed:break
    return {"outcome":"optimal_bound","region":sorted(reach),"values":encdist(vals),
            "policy":policy}


def solve_simulation(p: Simulation, stats: dict | None = None) -> dict:
    stats = stats if stats is not None else {}; stats["transport_calls"]=0
    m,n=len(p.left),len(p.right)
    live={(s,t) for s in range(m) for t in range(n) if p.base[s][t]};removed=[]
    def rel(): return tuple(tuple((s,t) in live for t in range(n)) for s in range(m))
    def coupling(s,t,a,b,r):
        stats["transport_calls"]+=1
        return solve_transport(Transport(p.left[s][a],p.right[t][b],r))
    while True:
        removal=None;r=rel()
        for s,t in sorted(live):
            for a in range(len(p.left[s])):
                obstructions=[]
                for b in range(len(p.right[t])):
                    c=coupling(s,t,a,b,r)
                    if c["bad_mass"][0]==0:break
                    obstructions.append(c["hall_subset"])
                else:
                    removal={"pair":[s,t],"left_action":a,"obstructions":obstructions}
                    break
            if removal is not None:break
        if removal is None:break
        removed.append(removal);live.remove(tuple(removal["pair"]))
    matches=[];r=rel()
    for s,t in sorted(live):
        for a in range(len(p.left[s])):
            for b in range(len(p.right[t])):
                c=coupling(s,t,a,b,r)
                if c["bad_mass"][0]==0:
                    matches.append({"pair":[s,t],"left_action":a,"right_action":b,"coupling":c})
                    break
            else:raise RuntimeError("unstable simulation fixed point")
    return {"removed":removed,"survivors":[list(x) for x in sorted(live)],"matches":matches}
