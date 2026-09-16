"""Classical repeated-attractor Büchi solver, with two rank certificates."""
from __future__ import annotations
from .models import Game, require


def _attractor(g: Game, universe: set[int], target: set[int], player: int):
    attr=set(target); rank={v:0 for v in target}; moves={}; rounds=0
    while True:
        fresh=[]
        for v in sorted(universe-attr):
            row=[w for w in g.edges[v] if w in universe]
            require(bool(row), 'internal non-total subarena')
            good=[w for w in row if w in attr]
            if (g.owner[v]==player and good) or (g.owner[v]!=player and len(good)==len(row)):
                fresh.append(v)
                if g.owner[v]==player:
                    moves[v]=min(good,key=lambda w:(rank[w],w))
        if not fresh:
            return attr,rank,moves,rounds
        rounds+=1
        for v in fresh:
            rank[v]=rounds
        attr.update(fresh)


def solve(g: Game) -> dict:
    g.validate(); live=set(range(g.n)); counter={}; removed=[]
    passes=0; attractor_rounds=0
    while live:
        passes+=1
        a,rank,policy,rounds=_attractor(g,live,live & g.accepting,0)
        attractor_rounds+=rounds
        bad=live-a
        if not bad:
            winrank=rank; winpolicy=policy
            break
        lost,_,escape,rounds=_attractor(g,live,bad,1)
        attractor_rounds+=rounds
        for v in sorted(lost):
            if g.owner[v]==1:
                if v in bad:
                    counter[v]=next(w for w in g.edges[v] if w in bad)
                else:
                    counter[v]=escape[v]
        removed.append(sorted(lost)); live-=lost
    else:
        winrank={}; winpolicy={}
    win=set(live); lose=set(range(g.n))-win
    # At accepting protagonist vertices only closure, not descent, is required.
    for v in sorted(win & g.accepting):
        if g.owner[v]==0:
            winpolicy[v]=next(w for w in g.edges[v] if w in win)
    positive={'kind':'buchi_win','region':sorted(win),
              'rank':[winrank.get(v) for v in range(g.n)],
              'policy':[winpolicy.get(v) for v in range(g.n)]}
    # Compute an independent local ranking for the fixed negative strategy graph.
    # Positive edge weights occur only on departure from accepting vertices.
    lr={v:0 for v in lose}
    for _ in range(g.n+1):
        new={}
        for v in sorted(lose):
            row=(counter[v],) if g.owner[v]==1 else g.edges[v]
            require(all(w in lose for w in row), 'losing strategy not closed')
            new[v]=max(lr[w]+int(v in g.accepting) for w in row)
        if new==lr:
            break
        lr=new
    else:
        raise RuntimeError('positive cycle in synthesized co-Buchi strategy')
    negative={'kind':'buchi_lose','region':sorted(lose),
              'rank':[lr.get(v) for v in range(g.n)],
              'policy':[counter.get(v) for v in range(g.n)]}
    return {'winning':positive,'losing':negative,
            'stats':{'outer_passes':passes,'attractor_rounds':attractor_rounds,
                     'removed_layers':removed}}
