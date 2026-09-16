#!/usr/bin/env python3
"""Reproduce the seeded corpus; defaults never overwrite recorded results."""
from __future__ import annotations
import argparse, copy, json, platform, random, statistics, sys, time
from collections import Counter, defaultdict
from fractions import Fraction as Q
from pathlib import Path
from forgeq import search as S, checker as C
import oracles as O

SEED = 20260915


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=Path('../reproduced-results'))
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    rng, records, mutations, unknowns = random.Random(SEED), [], [], []
    def counts(n, total):
        a = [0]*n
        for _ in range(total): a[rng.randrange(n)] += 1
        return a
    def law(n, total=6): return [Q(x,total) for x in counts(n,total)]
    def put(worker, problem, producer, oracle, label='seeded'):
        problem = S.dump(problem)
        t = time.perf_counter_ns(); cert = producer(problem); search_ns = time.perf_counter_ns()-t
        if cert['kind'] == 'unknown':
            raise RuntimeError(f'unexpected unknown {worker}: {cert}')
        t = time.perf_counter_ns(); audit = C.audit(worker,problem,cert); check_ns=time.perf_counter_ns()-t
        if not audit['accepted']: raise RuntimeError((worker,audit,problem,cert))
        if not oracle(problem,cert): raise RuntimeError(('oracle mismatch',worker,problem,cert))
        record = {'id': f'{worker}-{sum(r["worker"]==worker for r in records):03d}',
                  'worker':worker,'label':label,'problem':problem,'certificate':cert,
                  'audit':audit,'independent_oracle':True,'search_ns':search_ns,'check_ns':check_ns,
                  'certificate_bytes':len(json.dumps(cert,separators=(',',':')).encode())}
        records.append(record)
        # One deliberately INVALID mutation per accepted record. An arbitrary
        # weakening of a bound need not be invalid, so mutations are explicit.
        bad=copy.deepcopy(cert)
        kind=cert['kind']
        if worker=='reach': bad['value'][problem['target'][0]]='0'
        elif worker=='runtime': bad['potential']=['0']*len(bad['potential'])
        elif worker=='transport':
            if kind=='hall': bad['left_set']=[];bad['neighbors']=[]
            else: bad['joint'][0][0]=str(Q(bad['joint'][0][0])+Q(1,10**30))
        elif worker=='bisimulation':
            if kind=='bisimulation': bad['couplings']=bad['couplings'][1:]
            else: bad['removals'].append({'pair':[-1,0],'cut':{'kind':'hall','left_set':[],'neighbors':[]}})
        elif worker=='contraction':
            joint=bad['joints'][0] if kind=='contraction' else bad['transport']['joint']
            joint[0][0]=str(Q(joint[0][0])+Q(1,10**30))
        elif worker=='polynomial_cost': bad['potential'][0]='1'
        result=C.audit(worker,problem,bad)
        if result['accepted']: raise RuntimeError(('mutation accepted',record['id']))
        mutations.append({'source':record['id'],'worker':worker,'certificate':bad,'audit':result})
    # Exact reachability: independent bounded supersolution-polytope vertices.
    for k in range(60):
        n=rng.randrange(3,5)
        actions=[[law(n) for _ in range(2)] for _ in range(n)]
        actions[-1]=[[Q(i==n-1) for i in range(n)]]
        actions[-2]=[[Q(i==n-2) for i in range(n)]]  # absorbing rejection
        if k%3==0: actions[0][0]=[Q(i==0) for i in range(n)]
        put('reach',{'actions':actions,'target':[n-1]},S.reachability,
            lambda p,c:list(map(Q,c['value']))==O.reach_vertices(p))
    # Uniform runtimes in forward-with-self-loop MDPs: backward exact oracle.
    def rt_oracle(p,c):
        n=len(p['actions']);v=[Q(0)]*n
        for i in reversed(range(n-1)):
            v[i]=max((1+sum(Q(row[j])*v[j] for j in range(i+1,n)))/(1-Q(row[i]))
                     for row in p['actions'][i])
        return v==list(map(Q,c['potential']))
    for _ in range(50):
        n=rng.randrange(2,6);actions=[]
        for s in range(n-1):
            choices=[]
            for a in range(2):
                stay=Q(rng.randrange(0,6),6)
                row=[Q(0)]*n;row[s]=stay
                tails=law(n-s-1)
                for j,z in enumerate(tails,s+1):row[j]=(1-stay)*z
                choices.append(row)
            actions.append(choices)
        actions.append([[Q(i==n-1) for i in range(n)]])
        put('runtime',{'actions':actions,'target':[n-1]},S.runtime,rt_oracle)
    # Transport independently checked by small integer contingency enumeration.
    for _ in range(180):
        n,m,total=rng.randrange(1,4),rng.randrange(1,4),rng.randrange(3,7)
        lc,rc=counts(n,total),counts(m,total)
        allowed=[(i,j) for i in range(n) for j in range(m) if rng.random()<.72]
        cost=[[rng.randrange(8) for _ in range(m)] for _ in range(n)]
        p=S.transport_problem([Q(x,total) for x in lc],[Q(x,total) for x in rc],allowed,cost)
        opt=O.integer_transport(lc,rc,cost,allowed)
        def oracle(p,c,opt=opt):
            if opt is None:return c['kind']=='hall'
            if c['kind']!='transport':return False
            return sum(Q(c['joint'][i][j])*Q(p['cost'][i][j])
                       for i in range(len(p['left'])) for j in range(len(p['right'])))==opt
        put('transport',p,S.transport,oracle)
    # Bisimulation: probability-to-block partition oracle, not coupling search.
    for k in range(120):
        n=rng.randrange(3,6);p=[law(n) for _ in range(n)];labels=[rng.randrange(3) for _ in range(n)]
        labels[0:3]=[0,1,2]
        if k%3==0:
            perm=list(range(n));rng.shuffle(perm)
            q=[[p[perm[i]][perm[j]] for j in range(n)] for i in range(n)]
            obs=[labels[perm[i]] for i in range(n)];start=[rng.randrange(n),0];start[1]=perm.index(start[0])
        else:
            q=[law(n) for _ in range(n)];obs=[rng.randrange(3) for _ in range(n)]
            start=[0,0];obs[0:3]=[0,1,2]  # force matching observations at the queried pair
        put('bisimulation',{'left':p,'right':q,'obs_left':labels,'obs_right':obs,'start':start},
            S.bisimulation,lambda p,c:(c['kind']=='bisimulation')==O.bisim_partition(p))
    # Reset/stay chains: discrete-metric optimum is total variation exactly.
    for k in range(60):
        n=rng.randrange(2,6);rate=Q(rng.randrange(1,6),6);rho=law(n)
        sigma=rho if k%3==0 else law(n)
        left=[[(1-rate)*rho[j]+rate*Q(i==j) for j in range(n)] for i in range(n)]
        right=[[(1-rate)*sigma[j]+rate*Q(i==j) for j in range(n)] for i in range(n)]
        eps=(1-rate)*O.total_variation(rho,sigma)
        chosen=rate if k%3!=2 else rate/2
        p={'left':left,'right':right,'distance':[[Q(i!=j) for j in range(n)] for i in range(n)],
           'rate':chosen,'error':eps}
        def oracle(p,c):
            valid=all(O.total_variation(p['left'][i],p['right'][j])<=Q(p['rate'])*Q(i!=j)+Q(p['error'])
                for i in range(len(p['left'])) for j in range(len(p['right'])))
            return (c['kind']=='contraction')==valid
        put('contraction',p,S.contraction,oracle)
    # Infinite-state walks: exact finite distributions, 12 prefixes per record.
    for k in range(50):
        degree=k%6; denominator=rng.randrange(7,22)
        up=rng.randrange(1,(denominator+1)//3); hold=rng.randrange(0,denominator-2*up)
        down=denominator-up-hold
        coeff=[rng.randrange(0,6) for _ in range(degree)]+[rng.randrange(1,6)]
        p={'jumps':[-1,0,1],'probabilities':[Q(down,denominator),Q(hold,denominator),Q(up,denominator)],'cost':coeff}
        put('polynomial_cost',p,S.polynomial_cost,
            lambda p,c:O.stopped_cost_check(p,c,start=4,horizon=12))
    # Explicit resource/fragment failures are retained separately, not negatives.
    controls=[('reach',{'actions':[[[0,1]],[[0,1]]],'target':[1]},lambda p:S.reachability(p,0)),
              ('runtime',{'actions':[[[1,0],[0,1]],[[0,1]]],'target':[1]},S.runtime),
              ('polynomial_cost',{'jumps':[-1,1],'probabilities':['1/2','1/2'],'cost':[1]},S.polynomial_cost),
              ('polynomial_cost',{'jumps':[-1,1],'probabilities':['2/3','1/3'],'cost':[1]},lambda p:S.polynomial_cost(p,0)),
              ('transport',S.transport_problem([1],[1]),lambda p:S.transport(p,0))]
    for worker,p,fn in controls:
        c=fn(p)
        if c['kind']!='unknown':raise RuntimeError('bad UNKNOWN control')
        unknowns.append({'worker':worker,'problem':p,'result':c,'permits_semantic_rejection':False})
    def save(name,x): (args.out/name).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
    save('certificates.json',records);save('mutations.json',mutations);save('unknown-controls.json',unknowns)
    rows=[]
    for worker in C.WORKERS:
        rs=[r for r in records if r['worker']==worker]
        rows.append({'worker':worker,'records':len(rs),'kinds':dict(Counter(r['certificate']['kind'] for r in rs)),
            'independent_oracle_agreements':sum(r['independent_oracle'] for r in rs),
            'distinct_problems':len({json.dumps(r['problem'],sort_keys=True) for r in rs}),
            'mutations_rejected':sum(m['worker']==worker for m in mutations),
            'search_ms_median':statistics.median(r['search_ns']/1e6 for r in rs),
            'check_ms_median':statistics.median(r['check_ns']/1e6 for r in rs),
            'search_ms_max':max(r['search_ns']/1e6 for r in rs),
            'check_ms_max':max(r['check_ns']/1e6 for r in rs),
            'certificate_bytes_max':max(r['certificate_bytes'] for r in rs)})
    summary={'seed':SEED,'python':sys.version,'platform':platform.platform(),
             'dependencies':'Python standard library only; invoked with -S',
             'workers':rows,'records':len(records),'rejected_mutations':len(mutations),
             'unknown_controls':len(unknowns),'lean_kernel_proofs':0,
             'polynomial_finite_horizon_checks':50*12,
             'reach_records_with_fractional_state':sum(any(0<Q(x)<1 for x in r['certificate']['value']) for r in records if r['worker']=='reach'),
             'negative_bisim_with_nonempty_trace':sum(bool(r['certificate']['removals']) for r in records if r['certificate']['kind']=='no_bisimulation'),
             'note':'Times are single-process local measurements, not Lean tactic benchmarks.'}
    save('summary.json',summary)
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
