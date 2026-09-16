"""Replay ONLY: no solver, graph-search, elimination or synthesis imports.

These are executable research checkers, NOT formally verified checkers.
Positive and negative certificates have different logical meanings.
"""
from __future__ import annotations
from fractions import Fraction as F
from .models import PDS, Game, Chain, require, natural


def _triple(p: PDS, value: object) -> tuple[int,int,int]:
    require(isinstance(value,(list,tuple)) and len(value)==3, 'summary triple')
    x,a,y=value
    require(natural(x,p.n) and natural(y,p.n) and natural(a,p.alphabet), 'summary bounds')
    return x,a,y


def check_pds(p: PDS, cert: dict) -> dict:
    """Check a productive pop-summary DAG OR a closed exclusion relation."""
    p.validate()
    if cert.get('kind')=='pds_reach':
        nodes=cert['nodes']
        require(len(nodes)<=p.n*p.n*p.alphabet, 'too many distinct summaries')
        triples=[]; seen=set(); lengths=[]
        for i,node in enumerate(nodes):
            tr=_triple(p,node['triple'])
            require(tr not in seen, 'duplicate summary')
            seen.add(tr)
            rid=node['rule']
            require(natural(rid,len(p.rules)), 'rule index')
            r=p.rules[rid]
            require(tr[:2]==(r.p,r.a), 'rule head differs')
            children=node['children']
            require(len(children)==len(r.rhs), 'wrong number of child summaries')
            q=r.q
            size=1
            for symbol,j in zip(r.rhs,children):
                require(natural(j,i), 'cyclic/forward/invalid provenance')
                x,a,y=triples[j]
                require((x,a)==(q,symbol), 'child cannot continue stack pop')
                q=y; size+=lengths[j]
            require(q==tr[2], 'wrong final control')
            triples.append(tr); lengths.append(size)
        chain=cert['chain']
        require(len(chain)==len(p.stack), 'initial stack coverage')
        q=p.start; steps=0
        for symbol,j in zip(p.stack,chain):
            require(natural(j,len(nodes)), 'root reference')
            x,a,y=triples[j]
            require((x,a)==(q,symbol), 'root chain mismatch')
            q=y; steps+=lengths[j]
        require(q in p.finals, 'wrong query target')
        return {'outcome':'reachable','dag_nodes':len(nodes),'expanded_steps':steps}
    require(cert.get('kind')=='pds_exclude', 'wrong pushdown certificate kind')
    raw=cert['relation']
    relation={_triple(p,tr) for tr in raw}
    require(len(raw)==len(relation), 'duplicate summary in exclusion relation')
    # This exhaustive local closure audit is NOT the agenda-based search.
    for r in p.rules:
        if not r.rhs:
            require((r.p,r.a,r.q) in relation, 'missing pop base')
        elif len(r.rhs)==1:
            b=r.rhs[0]
            for t in range(p.n):
                if (r.q,b,t) in relation:
                    require((r.p,r.a,t) in relation, 'unary closure failure')
        else:
            b,c=r.rhs
            for m in range(p.n):
                for t in range(p.n):
                    if (r.q,b,m) in relation and (m,c,t) in relation:
                        require((r.p,r.a,t) in relation, 'binary closure failure')
    reachable={p.start}
    for a in p.stack:
        reachable={t for x in reachable for t in range(p.n) if (x,a,t) in relation}
    require(not (reachable & p.finals), 'relation admits the requested target')
    return {'outcome':'unreachable','summaries':len(relation)}


def check_game(g: Game, cert: dict, start: int) -> dict:
    """Check a positional Büchi strategy or a co-Büchi counterstrategy."""
    g.validate(); require(natural(start,g.n), 'game start')
    raw=cert['region']; region=set(raw)
    require(len(raw)==len(region) and start in region, 'region/start')
    require(all(natural(v,g.n) for v in region), 'region bounds')
    ranks=cert['rank']; policy=cert['policy']
    require(len(ranks)==len(policy)==g.n, 'rank/policy dimensions')
    for v in range(g.n):
        if v in region:
            require(natural(ranks[v]), 'nonnegative rank required')
        else:
            require(ranks[v] is None and policy[v] is None, 'outside-region payload')
    positive=cert.get('kind')=='buchi_win'
    require(positive or cert.get('kind')=='buchi_lose', 'wrong game certificate kind')
    controller=0 if positive else 1
    for v in sorted(region):
        if g.owner[v]==controller:
            w=policy[v]
            require(natural(w,g.n) and w in g.edges[v], 'illegal strategy move')
            allowed=(w,)
        else:
            require(policy[v] is None, 'policy controls the opponent')
            allowed=g.edges[v]
        for w in allowed:
            require(w in region, 'strategy region not closed')
            if positive:
                if v not in g.accepting:
                    require(ranks[v]>ranks[w], 'nonaccepting progress failure')
            else:
                require(ranks[v]>=ranks[w]+int(v in g.accepting), 'co-Buchi progress failure')
    return {'outcome':'winning' if positive else 'losing','region_size':len(region),
            'max_rank':max(ranks[v] for v in region)}


def check_chain(c: Chain, cert: dict) -> dict:
    """Check exact absorption values with a properness witness, or a trap."""
    c.validate()
    if cert.get('kind')=='mc_trap':
        raw=cert['closed']; closed=set(raw)
        require(raw and len(raw)==len(closed), 'nonempty duplicate-free trap')
        require(all(natural(v,c.n) for v in closed), 'trap state bounds')
        require(not(closed & c.terminal), 'trap contains terminal state')
        for v in closed:
            require(all(p==0 or w in closed for w,p in enumerate(c.matrix[v])), 'trap not closed')
        path=cert['path']
        require(path and all(natural(v,c.n) for v in path), 'path states')
        require(path[0]==c.start and path[-1] in closed, 'path query mismatch')
        probability=F(1)
        for v,w in zip(path,path[1:]):
            require(c.matrix[v][w]>0, 'zero-probability path')
            probability*=c.matrix[v][w]
        return {'outcome':'not_almost_sure','failure_probability_lower_bound':probability}
    require(cert.get('kind')=='mc_absorb', 'wrong chain certificate kind')
    raw=cert['support']; support=set(raw)
    require(len(raw)==len(support) and c.start in support, 'support/start')
    require(all(natural(v,c.n) for v in support), 'support bounds')
    h,v,u=cert['time'],cert['cost'],cert['value']
    require(len(h)==len(v)==len(u)==c.n, 'value dimensions')
    for s in range(c.n):
        if s not in support:
            require(h[s] is None and v[s] is None and u[s] is None, 'outside-support values')
            continue
        require(type(h[s]) is F and h[s]>=0, 'time potential')
        require(type(v[s]) is F and v[s]>=0, 'cost potential')
        require(type(u[s]) is F and 0<=u[s]<=1, 'absorption value')
        require(all(p==0 or t in support for t,p in enumerate(c.matrix[s])), 'support not closed')
        if s in c.terminal:
            require(h[s]==v[s]==0 and u[s]==c.payoff[s], 'terminal values')
        else:
            eh=sum((c.matrix[s][t]*h[t] for t in support),F(0))
            ev=sum((c.matrix[s][t]*v[t] for t in support),F(0))
            eu=sum((c.matrix[s][t]*u[t] for t in support),F(0))
            require(h[s]==1+eh, 'properness/time equation')
            require(v[s]==c.cost[s]+ev, 'cost equation')
            require(u[s]==eu, 'harmonic equation')
    return {'outcome':'almost_sure','expected_time':h[c.start],
            'expected_cost':v[c.start],'expected_terminal_payoff':u[c.start]}
