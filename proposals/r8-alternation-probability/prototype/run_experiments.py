#!/usr/bin/env python3
"""Deterministic differential/mutation suite; standard library only.

Default writes to a new reproduced-results directory; recorded results are not
silently overwritten. Diagnostic failures and partial corpora are retained.
"""
from __future__ import annotations
import argparse, json, platform, random, time, traceback, unittest
from pathlib import Path
from collections import Counter
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
from forge_ap.models import *
from forge_ap import search, check
from tests import oracles


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',default='reproduced-results')
    ap.add_argument('--quick',action='store_true');args=ap.parse_args()
    out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
    if (out/'report.json').exists():raise SystemExit('Choose a fresh output directory.')
    rng=random.Random(20260915);records=[];counts={};metrics={};start=time.perf_counter()
    report={'seed':20260915,'python':platform.python_version(),'platform':platform.platform(),
            'quick':args.quick,'status':'RUNNING','units':{},'lean':'NOT_RUN'}
    def save():
        (out/'corpus.json').write_text(json.dumps(records,separators=(',',':'))+'\n')
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    def record(kind,p,c):
        rec={'id':f'{kind}-{counts[kind]["cases"]:04d}','problem':p.obj(),'certificate':c}
        check.check_record(rec);records.append(rec);counts[kind]['cases']+=1
        counts[kind]['accepted_records']+=1
    def reject(kind,p,c):
        try:check.check_record({'id':'mutation','problem':p.obj(),'certificate':c})
        except Invalid:counts[kind]['rejected_mutations']+=1
        else:raise AssertionError(f'accepted invalid {kind} mutation')
    def init(kind):counts[kind]=Counter();metrics[kind]=Counter()
    def dist(n):
        weights=[rng.randrange(0,5) for _ in range(n)]
        if not any(weights):weights[rng.randrange(n)]=1
        den=sum(weights);return tuple(Q(w,den) for w in weights)
    try:
        with (out/'unittest.txt').open('w') as stream:
            result=unittest.TextTestRunner(stream=stream,verbosity=2).run(
                unittest.defaultTestLoader.discover(str(Path(__file__).parent/'tests'),pattern='test_*.py'))
        report['regression_tests']={'run':result.testsRun,'failures':len(result.failures),'errors':len(result.errors)}
        assert result.wasSuccessful()
        init('parity')
        # Exhaustive total one- and two-vertex games, owners 0/1, priorities 0..3.
        arenas=[]
        for n in (1,2):
            successors=[tuple(i for i in range(n) if mask>>i&1) for mask in range(1,1<<n)]
            for owners in product(range(2),repeat=n):
                for priorities in product(range(4),repeat=n):
                    for edges in product(successors,repeat=n):arenas.append(Arena(owners,priorities,edges))
        report['exhaustive_parity_arenas']=len(arenas)
        for _ in range(25 if args.quick else 300):
            n=rng.randrange(3,9)
            edges=tuple(tuple(sorted(rng.sample(range(n),rng.randrange(1,min(n,2)+1)))) for _ in range(n))
            arenas.append(Arena(tuple(rng.randrange(2) for _ in range(n)),
                                tuple(rng.randrange(6) for _ in range(n)),edges))
        for p in arenas:
            stats={};c=search.solve_parity(p,stats);expected=oracles.parity_regions(p)
            assert all(set(c['regions'][i]['vertices'])==expected[i] for i in (0,1))
            metrics['parity'].update(stats);record('parity',p,c);counts['parity']['oracle_comparisons']+=1
            # Delete a vertex from the required whole-arena partition.
            d=deepcopy(c)
            for region in d['regions']:
                if 0 in region['vertices']:region['vertices'].remove(0);break
            reject('parity',p,d)
            # Deliberately violate one applicable rank constraint, when it exists.
            mutated=False
            for i,region in enumerate(c['regions']):
                w=set(region['vertices'])
                for k,r in enumerate(region['ranks']):
                    for v in sorted(w):
                        ts=[region['strategy'][v]] if p.owner[v]==i else p.edges[v]
                        for t in ts:
                            if p.priority[v]==r['priority'] and p.priority[t]<=r['priority']:
                                d=deepcopy(c);d['regions'][i]['ranks'][k]['values'][v]=r['values'][t]
                                reject('parity',p,d);mutated=True;break
                        if mutated:break
                    if mutated:break
                if mutated:break
        init('transport')
        for _ in range(30 if args.quick else 400):
            m,n=rng.randrange(1,7),rng.randrange(1,7)
            p=Transport(dist(m),dist(n),tuple(tuple(bool(rng.randrange(2)) for _ in range(n)) for _ in range(m)))
            stats={};c=search.solve_transport(p,stats);delta=Q(*c['bad_mass'])
            assert delta==oracles.hall_defect(p.mu,p.nu,p.relation)
            independent=sum((p.mu[i]*p.nu[j] for i in range(m) for j in range(n)
                             if not p.relation[i][j]),Q(0))
            counts['transport']['strict_improvement_over_independent']+=int(delta<independent)
            counts['transport']['zero_defect']+=int(delta==0)
            counts['transport']['positive_defect']+=int(delta>0)
            metrics['transport'].update(stats);record('transport',p,c);counts['transport']['oracle_comparisons']+=1
            d=deepcopy(c);d['joint'][0][0]=encq(Q(*d['joint'][0][0])+1);reject('transport',p,d)
            if delta>0:
                d=deepcopy(c);d['hall_subset']=[];reject('transport',p,d)
        init('mdp')
        for case in range(24 if args.quick else 180):
            n=rng.randrange(2,5);actions=[]
            for s in range(n-1):
                aa=[]
                for _ in range(rng.randrange(1,3)):
                    d=list(dist(n))
                    if case%2==0:
                        d=[x/2 for x in d];d[-1]+=Q(1,2)
                    aa.append(tuple(d))
                actions.append(tuple(aa))
            actions.append((tuple(Q(int(t==n-1)) for t in range(n)),))
            p=MDP(tuple(actions),(n-1,),0);stats={};c=search.solve_mdp(p,stats)
            expected=oracles.worst_mdp(p)
            assert (c['outcome']=='nontermination')==(expected is None)
            if expected is not None:assert Q(*c['values'][p.start])==expected
            counts['mdp'][c['outcome']]+=1;metrics['mdp'].update(stats)
            record('mdp',p,c);counts['mdp']['oracle_comparisons']+=1
            d=deepcopy(c)
            if c['outcome']=='optimal_bound':d['values'][p.start]=[0,1]
            else:d['probability_lower']=[0,1]
            reject('mdp',p,d)
        init('simulation')
        for _ in range(12 if args.quick else 100):
            m,n=rng.randrange(1,3),rng.randrange(1,4)
            left=tuple(tuple(dist(m) for _ in range(rng.randrange(1,3))) for s in range(m))
            right=tuple(tuple(dist(n) for _ in range(rng.randrange(1,3))) for t in range(n))
            base=tuple(tuple(bool(rng.randrange(2)) for t in range(n)) for s in range(m))
            p=Simulation(left,right,base);stats={};c=search.solve_simulation(p,stats)
            expected=oracles.greatest_simulation(p)
            assert {tuple(x) for x in c['survivors']}==expected
            metrics['simulation'].update(stats);record('simulation',p,c)
            counts['simulation']['oracle_comparisons']+=1
            counts['simulation']['removed_pairs']+=len(c['removed'])
            counts['simulation']['surviving_pairs']+=len(c['survivors'])
            if c['removed']:
                d=deepcopy(c);d['removed'][0]['obstructions'][0]=[];reject('simulation',p,d)
            if c['matches']:
                d=deepcopy(c);d['matches'].pop();reject('simulation',p,d)
        report['status']='PASS';report['units']={k:dict(v) for k,v in counts.items()}
        report['algorithm_counters']={k:dict(v) for k,v in metrics.items()}
        report['elapsed_seconds']=time.perf_counter()-start
        report['claims']=['exact finite-model Python differential tests only',
                          'no tactic baseline was executed','no Lean compiler was run']
        save();print(json.dumps(report,indent=2))
    except BaseException:
        report['status']='FAIL';report['units']={k:dict(v) for k,v in counts.items()}
        report['elapsed_seconds']=time.perf_counter()-start
        (out/'failure.txt').write_text(traceback.format_exc());save();raise

if __name__=='__main__':main()
