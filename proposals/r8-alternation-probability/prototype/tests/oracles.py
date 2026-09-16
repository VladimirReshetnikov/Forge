"""Small independent exhaustive oracles. No proposer or checker imports.

Parity: strategy profiles and actual eventual cycles.
Transport: enumerate all weighted Hall inequalities, without max flow.
MDP: enumerate policies, graph reachability, determinants/Cramer's rule.
Simulation: enumerate every subrelation, not a deletion fixed-point algorithm.
"""
from fractions import Fraction as Q
from itertools import product, permutations


def parity_regions(p):
    owned=[[v for v in range(p.n) if p.owner[v]==player] for player in (0,1)]
    policies=[]
    for player in (0,1):
        policies.append([dict(zip(owned[player],choices))
                         for choices in product(*(p.edges[v] for v in owned[player]))])
    profiles=[]
    for a in policies[0]:
        row=[]
        for b in policies[1]:
            successor={**a,**b};wins=[]
            for start in range(p.n):
                walk=[];seen={};cur=start
                while cur not in seen:
                    seen[cur]=len(walk);walk.append(cur);cur=successor[cur]
                wins.append(max(p.priority[v] for v in walk[seen[cur]:])%2)
            row.append(wins)
        profiles.append(row)
    zero={v for v in range(p.n) if any(all(profiles[a][b][v]==0
                    for b in range(len(policies[1]))) for a in range(len(policies[0])))}
    one={v for v in range(p.n) if any(all(profiles[a][b][v]==1
                    for a in range(len(policies[0]))) for b in range(len(policies[1])))}
    assert not zero & one and zero|one==set(range(p.n))
    return zero,one


def hall_defect(mu,nu,relation):
    best=Q(0)
    for mask in range(1<<len(mu)):
        a=[i for i in range(len(mu)) if mask>>i&1]
        neighbors=[j for j in range(len(nu)) if any(relation[i][j] for i in a)]
        best=max(best,sum((mu[i] for i in a),Q(0))-sum((nu[j] for j in neighbors),Q(0)))
    return best


def determinant(a):
    n=len(a);total=Q(0)
    for perm in permutations(range(n)):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n))
        term=Q(sign)
        for i,j in enumerate(perm):term*=a[i][j]
        total+=term
    return total


def worst_mdp(p):
    terminal=set(p.terminal);nonterminal=[s for s in range(p.n) if s not in terminal]
    worst=Q(0)
    for choices in product(*(range(len(p.actions[s])) for s in nonterminal)):
        policy=dict(zip(nonterminal,choices))
        edges=[{t for t,x in enumerate(p.actions[s][policy.get(s,0)]) if x>0}
               for s in range(p.n)]
        reachable={p.start}
        for _ in range(p.n):reachable|={t for s in list(reachable) for t in edges[s]}
        to_terminal=set(terminal)
        for _ in range(p.n):
            to_terminal|={s for s in range(p.n) if edges[s]&to_terminal}
        if reachable-to_terminal:return None
        states=sorted(reachable-terminal)
        if not states:continue
        a=[[Q(int(s==t))-p.actions[s][policy[s]][t] for t in states] for s in states]
        denominator=determinant(a);assert denominator!=0
        index=states.index(p.start)
        replaced=[row.copy() for row in a]
        for row in replaced:row[index]=Q(1)
        worst=max(worst,determinant(replaced)/denominator)
    return worst


def greatest_simulation(p):
    m,n=len(p.left),len(p.right)
    base=[(s,t) for s in range(m) for t in range(n) if p.base[s][t]]
    greatest=set()
    for mask in range(1<<len(base)):
        candidate={base[k] for k in range(len(base)) if mask>>k&1}
        relation=tuple(tuple((s,t) in candidate for t in range(n)) for s in range(m))
        good=True
        for s,t in candidate:
            for left in p.left[s]:
                if not any(hall_defect(left,right,relation)==0 for right in p.right[t]):
                    good=False;break
            if not good:break
        if good:greatest|=candidate
    return greatest
