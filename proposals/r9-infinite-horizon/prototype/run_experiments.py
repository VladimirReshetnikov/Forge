#!/usr/bin/env python3
"""Reproduce all experiments. Defaults never overwrite the recorded results."""
from __future__ import annotations
import argparse, itertools, platform, random, sys, time
from collections import Counter
from pathlib import Path
from fractions import Fraction as F
from forge_horizon.models import PDS,Rule,Game,Chain
from forge_horizon import pushdown,games,markov
from forge_horizon.checkers import check_pds,check_game,check_chain
from forge_horizon.codec import dumps,pack_model
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tests'))
from oracles import (pds_bfs,expanded_pds_trace,game_oracle,chain_acyclic,
                     chain_cramer,chain_as_oracle)

SEED=20260915

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path,
        default=Path(__file__).resolve().parents[1]/'reproduced-results')
    ap.add_argument('--quick',action='store_true',help='only exhaust games up to size two')
    args=ap.parse_args(); args.output.mkdir(parents=True,exist_ok=True)
    rng=random.Random(SEED); rows={}; records=[]; starttime=time.perf_counter()
    timings=Counter(); counts=Counter(); stats={}
    def record(group,model,certificate,answer,start=None):
        item={'group':group,'case':counts[group],'problem':pack_model(model),
              'certificate':certificate,'expected':answer}
        if start is not None:item['start']=start
        records.append(item); counts[group]+=1
    def pcase(group,p):
        t=time.perf_counter(); cert=pushdown.solve(p); timings['pds_search']+=time.perf_counter()-t
        t=time.perf_counter(); ans=check_pds(p,cert); timings['pds_check']+=time.perf_counter()-t
        record(group,p,cert,ans)
        return cert,ans
    # Complete direct-state oracle because no transition increases stack length.
    for k in range(500):
        n=rng.randint(1,4); a=rng.randint(1,3)
        rules=tuple(Rule(rng.randrange(n),rng.randrange(a),rng.randrange(n),
                         tuple(rng.randrange(a) for _ in range(rng.randrange(2))))
                    for _ in range(rng.randrange(1,15)))
        p=PDS(n,a,rules,rng.randrange(n),tuple(rng.randrange(a) for _ in range(rng.randrange(4))),
              frozenset(q for q in range(n) if rng.randrange(2)))
        cert,ans=pcase('pds_non_growing',p)
        found,complete,_=pds_bfs(p,len(p.stack)); assert complete
        assert found==(ans['outcome']=='reachable')
        if found:assert expanded_pds_trace(p,cert)==ans['expanded_steps']
    bounded=Counter()
    for k in range(250):
        n=2;a=2
        rules=tuple(Rule(rng.randrange(n),rng.randrange(a),rng.randrange(n),
                         tuple(rng.randrange(a) for _ in range(rng.randrange(3))))
                    for _ in range(rng.randrange(1,10)))
        p=PDS(n,a,rules,rng.randrange(n),tuple(rng.randrange(a) for _ in range(rng.randint(1,2))),
              frozenset({rng.randrange(n)}))
        cert,ans=pcase('pds_general',p)
        found,complete,_=pds_bfs(p,6)
        bounded['found' if found else 'complete_negative' if complete else 'truncated_unknown']+=1
        if found or complete:assert found==(ans['outcome']=='reachable')
        if ans['outcome']=='reachable':
            steps=expanded_pds_trace(p,cert)
            if steps is not None:assert steps==ans['expanded_steps']
    stats['pds_general_bounded_oracle']=dict(bounded)
    for k in range(100):
        rules=tuple(Rule(rng.randrange(2),rng.randrange(2),rng.randrange(2),
                         tuple(rng.randrange(2) for _ in range(rng.randrange(2)))) for _ in range(7))
        p=PDS(2,2,rules,0,tuple(rng.randrange(2) for _ in range(rng.randrange(4))),frozenset())
        delta=tuple(tuple(rng.randrange(3) for _ in range(2)) for _ in range(3))
        initial=tuple(rng.randrange(3) for _ in range(2)); accepting=frozenset({rng.randrange(3)})
        def target(q,w):
            state=initial[q]
            for letter in w:state=delta[state][letter]
            return state in accepting
        found,complete,_=pds_bfs(p,len(p.stack),target); assert complete
        compiled=pushdown.compile_regular_target(p,delta,initial,accepting)
        _,ans=pcase('pds_regular_target',compiled)
        assert found==(ans['outcome']=='reachable')
    for depth in range(31):
        rules=(Rule(0,0,0,()),)+tuple(Rule(0,i,0,(i-1,i-1)) for i in range(1,depth+1))
        p=PDS(1,depth+1,rules,0,(depth,),frozenset({0}))
        cert,ans=pcase('pds_compressed',p)
        assert ans['expanded_steps']==2**(depth+1)-1 and ans['dag_nodes']==depth+1
        if depth<=10:assert expanded_pds_trace(p,cert)==ans['expanded_steps']
    stats['compressed_depth30']=ans
    # All total arenas, all owner maps, and all accepting sets through size 3.
    # Each arena is one case; all start vertices are checked, but not counted as arenas.
    game_starts=0; game_outcomes=Counter()
    def gcase(group,g):
        nonlocal game_starts
        t=time.perf_counter(); result=games.solve(g); timings['game_search']+=time.perf_counter()-t
        t=time.perf_counter(); w,l=game_oracle(g); timings['game_oracle']+=time.perf_counter()-t
        assert set(result['winning']['region'])==w and set(result['losing']['region'])==l
        for region,key in ((w,'winning'),(l,'losing')):
            if not region:continue
            cert=result[key]
            for s in sorted(region):
                t=time.perf_counter();ans=check_game(g,cert,s);timings['game_check']+=time.perf_counter()-t
                game_starts+=1;game_outcomes[ans['outcome']]+=1
            # Store one reusable region certificate, with a representative start.
            records.append({'group':group,'case':counts[group],'problem':pack_model(g),
                            'certificate':cert,'start':min(region),'expected':ans})
        counts[group]+=1
    maxn=2 if args.quick else 3
    for n in range(1,maxn+1):
        rows_nonempty=[tuple(v for v in range(n) if mask&(1<<v)) for mask in range(1,1<<n)]
        for edges in itertools.product(rows_nonempty,repeat=n):
            for owner in itertools.product((0,1),repeat=n):
                for mask in range(1<<n):
                    gcase('games_exhaustive',Game(owner,edges,frozenset(v for v in range(n) if mask&(1<<v))))
    for k in range(200):
        n=rng.randint(4,7)
        edges=tuple(tuple(sorted(rng.sample(range(n),rng.randint(1,min(3,n))))) for _ in range(n))
        gcase('games_random',Game(tuple(rng.randrange(2) for _ in range(n)),edges,
                                 frozenset(v for v in range(n) if rng.randrange(2))))
    stats['game_start_replays']=game_starts;stats['game_start_outcomes']=dict(game_outcomes)
    def mcase(group,c):
        t=time.perf_counter();cert=markov.solve(c);timings['mc_search']+=time.perf_counter()-t
        t=time.perf_counter();ans=check_chain(c,cert);timings['mc_check']+=time.perf_counter()-t
        record(group,c,cert,ans);return cert,ans
    def row(weights):
        total=sum(weights);assert total>0
        return tuple(F(x,total) for x in weights)
    for k in range(200):
        n=rng.randint(3,9);matrix=[]
        for s in range(n):
            if s>=n-2:matrix.append(tuple(F(int(t==s)) for t in range(n)))
            else:
                weights=[0]*(s+1)+[rng.randrange(5) for _ in range(n-s-1)]
                if not sum(weights):weights[-1]=1
                matrix.append(row(weights))
        c=Chain(tuple(matrix),frozenset({n-2,n-1}),tuple(F(int(t==n-1)) for t in range(n)),
                tuple(F(rng.randrange(5)) if t<n-2 else F(0) for t in range(n)))
        cert,ans=mcase('mc_acyclic',c);h,v,u=chain_acyclic(c)
        assert (ans['expected_time'],ans['expected_cost'],ans['expected_terminal_payoff'])==(h[0],v[0],u[0])
    for k in range(150):
        n=rng.randint(3,6);matrix=[]
        for s in range(n):
            if s>=n-2:matrix.append(tuple(F(int(t==s)) for t in range(n)))
            else:matrix.append(row([rng.randrange(4) for _ in range(n-2)]+[rng.randint(1,4),rng.randint(1,4)]))
        c=Chain(tuple(matrix),frozenset({n-2,n-1}),tuple(F(int(t==n-1)) for t in range(n)),
                tuple(F(rng.randint(0,7),rng.randint(1,4)) if t<n-2 else F(0) for t in range(n)))
        cert,ans=mcase('mc_cyclic_cramer',c);h,v,u=chain_cramer(c)
        assert (ans['expected_time'],ans['expected_cost'],ans['expected_terminal_payoff'])==(h[0],v[0],u[0])
    for d in range(1,61):
        c=Chain(((1-F(1,d),F(1,d)),(F(0),F(1))),frozenset({1}),(F(0),F(1)),(F(3,2),F(0)))
        _,ans=mcase('mc_geometric',c)
        assert ans['expected_time']==d and ans['expected_cost']==F(3*d,2) and ans['expected_terminal_payoff']==1
    for d in range(2,62):
        p=F(1,d)
        c=Chain(((F(0),1-p,p,F(0)),(F(0),F(1),F(0),F(0)),
                 (F(0),F(0),F(1,2),F(1,2)),(F(0),F(0),F(1,3),F(2,3))),
                frozenset({1}),(F(0),F(1),F(0),F(0)),(F(1),F(0),F(1),F(1)))
        _,ans=mcase('mc_traps',c)
        assert ans['failure_probability_lower_bound']==p
    for k in range(300):
        n=4;matrix=[]
        for s in range(n-1):
            weights=[rng.randrange(3) for _ in range(n)]
            if not sum(weights):weights[s]=1
            matrix.append(row(weights))
        matrix.append((F(0),F(0),F(0),F(1)))
        c=Chain(tuple(matrix),frozenset({3}),(F(0),F(0),F(0),F(1)),(F(1),F(1),F(1),F(0)))
        _,ans=mcase('mc_arbitrary',c)
        assert (ans['outcome']=='almost_sure')==chain_as_oracle(c)
    outcome_counts={group:dict(Counter(r['expected']['outcome'] for r in records if r['group']==group))
                    for group in counts}
    summary={'seed':SEED,'python':sys.version,'platform':platform.platform(),'quick':args.quick,
             'case_counts':dict(counts),'certificate_outcomes':outcome_counts,
             'record_count':len(records),'timings_seconds':dict(timings),'stats':stats,
             'total_wall_seconds':time.perf_counter()-starttime,
             'lean_status':'NOT_RUN: Lean executable unavailable; no tactic comparison',
             'scope':'Python prototype results, not formal verification; timing excludes file serialization.'}
    (args.output/'certificates.json').write_text(dumps(records))
    (args.output/'summary.json').write_text(dumps(summary))
    print(dumps(summary))

if __name__=='__main__':main()
