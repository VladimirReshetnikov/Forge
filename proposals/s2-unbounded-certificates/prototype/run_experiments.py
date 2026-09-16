#!/usr/bin/env python3
"""Deterministic experiments. Every run gets a fresh output directory.

No external packages; run as python -S run_experiments.py --out DIR.
An independent finite BFS is used only on exactly token-conserving nets.
Decimal computations are diagnostics, NOT acceptance authorities.
"""
from __future__ import annotations
import argparse, copy, csv, json, platform, random, sys, time, traceback
from collections import deque
from datetime import datetime, timezone
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from forge_unbounded.model import Petri, PPS, Term, encq, parse_problem, subject
from forge_unbounded.search import (petri_coverability, predecessor, pps_enclosure,
    critical_extinction, scalar_algebraic)
from forge_unbounded.verify import verify

SEED = 6071504


def compositions(total, n):
    if n == 1:
        return [(total,)]
    return [(k,) + tail for k in range(total + 1)
            for tail in compositions(total - k, n - 1)]


def bfs(p):
    """Independent FORWARD oracle. Refuse nets without exact conservation."""
    assert all(sum(a) == sum(b) for a, b in p.transitions)
    seen, work = {p.initial}, deque([p.initial])
    while work:
        m = work.popleft()
        if any(all(m[i] >= b[i] for i in range(p.d)) for b in p.targets):
            return True, len(seen)
        for a, b in p.transitions:
            if all(m[i] >= a[i] for i in range(p.d)):
                successor = tuple(m[i] + b[i] - a[i] for i in range(p.d))
                if successor not in seen:
                    seen.add(successor)
                    work.append(successor)
    return False, len(seen)


def decimal_q(x):
    return Decimal(x.numerator) / Decimal(x.denominator)


def numeric_lfp(p):
    """Independent high-precision monotone iteration, not a proof oracle."""
    with localcontext() as ctx:
        ctx.prec = 80
        x = [Decimal(0)] * p.d
        for k in range(2000):
            y = []
            for row in p.polynomials:
                z = Decimal(0)
                for t in row:
                    v = decimal_q(t.coefficient)
                    for i, power in enumerate(t.powers):
                        if power:
                            v *= x[i] ** power
                    z += v
                y.append(z)
            if max(abs(u - v) for u, v in zip(x, y)) < Decimal('1e-65'):
                return y, k + 1
            x = y
        raise AssertionError("diagnostic Decimal oracle did not converge")


def interval_contains(e, exact):
    return all(Q(*a) <= x <= Q(*b)
               for a, b, x in zip(e['lower'], e['upper'], exact))


def cubic(a, n=1):
    rows = []
    for i in range(n):
        z = (0,) * n
        power = [0] * n
        power[(i + 1) % n] = 3
        rows.append((Term(a, z), Term(1-a, tuple(power))))
    return PPS(tuple(rows))


class Run:
    def __init__(self, out):
        self.out = out
        out.mkdir(parents=True, exist_ok=False)
        self.rows, self.records, self.mutations = [], [], []
        self.rng = random.Random(SEED)
        self.start = time.perf_counter()

    def row(self, group, count, unit, **kw):
        self.rows.append(dict(group=group, cases=count, unit=unit, **kw))
        print(json.dumps(self.rows[-1]), flush=True)

    def record(self, name, problem, certificate):
        if not verify(problem, certificate):
            raise AssertionError(f"rejected producer output: {name}")
        self.records.append({'name':name,'problem':problem.data(),'certificate':certificate})

    def reject(self, name, p, c):
        assert not verify(p, c), name
        self.mutations.append({'name':name,'problem':p.data(),'certificate':c})

    def predecessor_tests(self):
        count = 0
        for pre, post, bad, mark in product(range(5), range(5), range(6), range(9)):
            minimum = predecessor((bad,), (pre,), (post,))[0]
            lhs = mark >= minimum
            rhs = mark >= pre and mark-pre+post >= bad
            assert lhs == rhs
            count += 1
        for _ in range(2000):
            n = self.rng.randint(2,4)
            pre, post, bad = [tuple(self.rng.randrange(6) for _ in range(n)) for _ in range(3)]
            mark = tuple(self.rng.randrange(10) for _ in range(n))
            threshold = predecessor(bad,pre,post)
            lhs = all(mark[i] >= threshold[i] for i in range(n))
            rhs = (all(mark[i] >= pre[i] for i in range(n)) and
                   all(mark[i]-pre[i]+post[i] >= bad[i] for i in range(n)))
            assert lhs == rhs
            count += 1
        self.row('predecessor_equivalence',count,'operational comparisons',passed=count)

    def petri_tests(self):
        transitions = [(a,b) for total in range(3)
                       for a in compositions(total,2) for b in compositions(total,2)]
        initials = [x for total in range(4) for x in compositions(total,2)]
        targets = [x for total in range(5) for x in compositions(total,2)]
        counts = {'safe':0,'coverable':0}
        start = time.perf_counter()
        case = 0
        for t, m, b in product(transitions, initials, targets):
            p = Petri(m,(t,),(b,))
            oracle,_ = bfs(p)
            c = petri_coverability(p)
            assert c['kind'] == ('coverable' if oracle else 'safe')
            self.record(f'petri-exhaustive-{case}',p,c)
            counts[c['kind']] += 1
            case += 1
        self.row('petri_exhaustive',case,'net/start/target queries',
                 oracle='complete forward BFS',seconds=time.perf_counter()-start,**counts)
        start = time.perf_counter()
        counts = {'safe':0,'coverable':0}
        for case in range(120):
            n = self.rng.choice([3,4])
            total = self.rng.randrange(5)
            m = self.rng.choice(compositions(total,n))
            ts=[]
            for _ in range(self.rng.randint(2,5)):
                k=self.rng.randrange(3)
                cs=compositions(k,n)
                ts.append((self.rng.choice(cs),self.rng.choice(cs)))
            target=self.rng.choice(compositions(self.rng.randrange(6),n))
            p=Petri(m,tuple(ts),(target,))
            oracle,_=bfs(p)
            c=petri_coverability(p)
            assert c['kind']==('coverable' if oracle else 'safe')
            self.record(f'petri-random-{case}',p,c)
            counts[c['kind']]+=1
        self.row('petri_random',120,'net/start/target queries',
                 oracle='complete forward BFS',seconds=time.perf_counter()-start,**counts)
        mutex=Petri((1,0,0),(((1,0,0),(0,1,0)),((0,1,0),(1,0,0)),
                           ((0,0,0),(0,0,1))),((0,2,0),))
        c=petri_coverability(mutex)
        assert c['kind']=='safe' and len(c['basis'])==3
        self.record('unbounded-mutex',mutex,c)
        pump=Petri((0,),(((0,),(1,)),),((25,),))
        c=petri_coverability(pump)
        assert c['kind']=='coverable' and len(c['word'])==25
        self.record('unbounded-pump',pump,c)
        capped=petri_coverability(pump,max_expansions=2)
        assert capped['kind']=='unknown' and not verify(pump,capped)
        self.mutations.append({'name':'budget-is-not-proof','problem':pump.data(),'certificate':capped})
        # Empty transitions, empty target set, and zero-dimensional markings.
        for k,p in enumerate([Petri((3,),(),()),Petri((),(),((),)),Petri((),(),())]):
            self.record(f'edge-petri-{k}',p,petri_coverability(p))
        self.row('petri_infinite_and_edges',6,'hand-designed cases',
                 safe_or_coverable=5,budget_unknown=1,mutex_basis=3,pump_trace_length=25)

    def scalar_tests(self):
        start=time.perf_counter()
        case=0
        steps=[]
        for ai in range(1,10):
            for bi in range(1,11-ai):
                a,b=Q(ai,10),Q(bi,10)
                p=PPS(((Term(a,(0,)),Term(1-a-b,(1,)),Term(b,(2,))),))
                e=pps_enclosure(p,target_bits=20,rounding_bits=40,max_steps=60)
                expected=min(Q(1),a/b)
                assert interval_contains(e,[expected]) and e['target_met']
                self.record(f'scalar-quadratic-{case}',p,e)
                steps.append(len(e['ledger']))
                case+=1
        self.row('pps_scalar_quadratic',case,'polynomial systems',
                 oracle='exact q=min(1,a/b)',all_widths_met=True,
                 max_newton_steps=max(steps),seconds=time.perf_counter()-start)

    def coupled_tests(self):
        start=time.perf_counter()
        maxsteps=0
        for case in range(30):
            n=self.rng.choice([2,3,4])
            rows=[]
            for i in range(n):
                zero=(0,)*n
                linear=[0]*n; linear[self.rng.randrange(n)]=1
                quad=[0]*n
                quad[self.rng.randrange(n)]+=1;quad[self.rng.randrange(n)]+=1
                rows.append((Term(Q(self.rng.randint(2,4),10),zero),
                             Term(Q(1,10),tuple(linear)),Term(Q(1,5),tuple(quad))))
            p=PPS(tuple(rows))
            e=pps_enclosure(p,target_bits=22,rounding_bits=42)
            approximate,iterations=numeric_lfp(p)
            with localcontext() as ctx:
                ctx.prec=80
                for l,u,x in zip(e['lower'],e['upper'],approximate):
                    assert decimal_q(Q(*l)) <= x <= decimal_q(Q(*u))
            assert e['target_met']
            maxsteps=max(maxsteps,len(e['ledger']))
            self.record(f'coupled-contractive-{case}',p,e)
        self.row('pps_coupled_contractive',30,'polynomial systems',
                 oracle='80-digit Decimal iteration (diagnostic)',all_widths_met=True,
                 max_newton_steps=maxsteps,seconds=time.perf_counter()-start)
        start=time.perf_counter()
        for n in [2,3,4]:
            for ai in range(1,9):
                a=Q(ai,20)
                p=cubic(a,n)
                e=pps_enclosure(p,target_bits=22,rounding_bits=42)
                with localcontext() as ctx:
                    ctx.prec=80
                    q=((1+4*decimal_q(a/(1-a))).sqrt()-1)/2
                    for l,u in zip(e['lower'],e['upper']):
                        assert decimal_q(Q(*l)) <= q <= decimal_q(Q(*u))
                assert e['target_met'] and 'contraction' in e
                self.record(f'coupled-supercritical-{n}-{ai}',p,e)
        self.row('pps_coupled_supercritical',24,'polynomial systems',
                 oracle='symmetric scalar algebraic solution (80-digit diagnostic)',
                 all_widths_met=True,seconds=time.perf_counter()-start)

    def critical_and_algebraic(self):
        start=time.perf_counter()
        for n in range(1,6):
            for bnum in range(1,6):
                b=Q(bnum,10)
                rows=[]
                for i in range(n):
                    zero=(0,)*n
                    linear=[0]*n;linear[i]=1
                    square=[0]*n;square[(i+1)%n]=2
                    rows.append((Term(b,zero),Term(1-2*b,tuple(linear)),Term(b,tuple(square))))
                p=PPS(tuple(rows))
                c=critical_extinction(p)
                assert c['kind']=='extinction_one'
                self.record(f'critical-cycle-{n}-{bnum}',p,c)
        # Row sums of the mean matrix are 1.8 and 0.2: an unweighted
        # sup-norm contraction cannot certify this, but positive weights can.
        weighted=PPS(((Term(Q(1,10),(0,0)),Term(Q(9,10),(0,2))),
                      (Term(Q(4,5),(0,0)),Term(Q(1,5),(1,0)))))
        c=critical_extinction(weighted)
        assert c['kind']=='extinction_one'
        self.record('weighted-subcritical',weighted,c)
        self.row('spectral_extinction',26,'polynomial systems',
                 exact_value='all coordinates equal 1',seconds=time.perf_counter()-start)
        for n in range(1,5):
            rows=[]
            for i in range(n):
                exponent=[0]*n;exponent[(i+1)%n]=1
                rows.append((Term(Q(1),tuple(exponent)),))
            p=PPS(tuple(rows))
            forged={'kind':'extinction_one','subject':subject(p),'weight':[[1,1]]*n}
            self.reject(f'singular-one-child-cycle-{n}',p,forged)
            assert critical_extinction(p)['kind']=='unknown'
        # Critical local recurrence has a double fixed point at 1.
        critical=PPS(((Term(Q(1,2),(0,)),Term(Q(1,2),(2,))),))
        e=pps_enclosure(critical,target_bits=20,rounding_bits=40)
        assert e['target_met'] and 'contraction' not in e
        self.record('critical-no-contraction',critical,e)
        for ai in range(1,9):
            a=Q(ai,20);p=cubic(a)
            e=pps_enclosure(p,target_bits=24,rounding_bits=44)
            certificate=scalar_algebraic(p,e,[-a,1-a,1-a],[Q(-1),Q(1)])
            self.record(f'algebraic-cubic-{ai}',p,certificate)
        self.row('algebraic_decoder',8,'isolated scalar least roots',accepted=8)
        p=cubic(Q(1,4))
        e=pps_enclosure(p,target_bits=20,rounding_bits=40,max_steps=0)
        assert verify(p,e) and not e['target_met']
        self.record('enclosure-budget-valid-but-wide',p,e)
        self.row('quantitative_boundary_controls',6,'hand-designed cases',
                 singular_rejected=4,critical_noncontractive=1,wide_enclosure=1)

    def mutation_tests(self):
        # Fixed, documented sample. Do not count arbitrary representation edits
        # as invalid: redundant basis elements may legitimately verify.
        candidates=self.records.copy()
        self.rng.shuffle(candidates)
        for k,rec in enumerate(candidates[:100]):
            p=parse_problem(rec['problem']);c=copy.deepcopy(rec['certificate'])
            c['subject']='wrong input'
            self.reject(f'wrong-subject-{k}',p,c)
        safes=[r for r in self.records if r['certificate']['kind']=='safe'
               and r['certificate']['basis'] and r['problem']['targets']]
        for k,rec in enumerate(safes[:60]):
            p=parse_problem(rec['problem']);c=copy.deepcopy(rec['certificate'])
            c['target_cover'][0]=len(c['basis'])
            self.reject(f'bad-cover-index-{k}',p,c)
        enclosures=[r for r in self.records if r['certificate']['kind']=='enclosure'
                    and r['certificate']['ledger']]
        for k,rec in enumerate(enclosures):
            p=parse_problem(rec['problem']);c=copy.deepcopy(rec['certificate'])
            if c['ledger'][0]['kind']=='newton':
                x=Q(*c['ledger'][0]['inverse'][0][0])+1
                c['ledger'][0]['inverse'][0][0]=encq(x)
                self.reject(f'wrong-newton-inverse-{k}',p,c)
        p=cubic(Q(1,4))
        e=pps_enclosure(p,target_bits=20,rounding_bits=40,max_steps=0)
        forged=copy.deepcopy(e)
        forged['ledger']=[{'kind':'kleene','next':[[1,1]]}]
        forged['lower']=[[1,1]];forged['target_met']=True
        self.reject('fixed-point-not-least',p,forged)
        forged=copy.deepcopy(e);forged['target_met']=True
        self.reject('width-lie',p,forged)
        accepted_algebraics=[r for r in self.records if r['certificate']['kind']=='algebraic_lfp']
        for k,rec in enumerate(accepted_algebraics):
            p=parse_problem(rec['problem']);c=copy.deepcopy(rec['certificate'])
            c['factor'][0]=[0,1]
            self.reject(f'wrong-algebraic-factor-{k}',p,c)
        self.row('rejection_controls',len(self.mutations),'deliberately invalid or non-authoritative receipts',
                 rejected=len(self.mutations))
        bad=[{'kind':'petri','initial':[-1],'transitions':[],'targets':[]},
             {'kind':'petri','initial':[True],'transitions':[],'targets':[]},
             {'kind':'pps','polynomials':[[{'coefficient':[-1,2],'powers':[1]}]]},
             {'kind':'pps','polynomials':[[{'coefficient':[2,1],'powers':[0]}]]},
             {'kind':'pps','polynomials':[[{'coefficient':[1,0],'powers':[0]}]]}]
        for d in bad:
            try:parse_problem(d)
            except ValueError:pass
            else:raise AssertionError('malformed input accepted')
        self.row('input_validation',len(bad),'malformed inputs',rejected=len(bad))

    def write(self,status,exception=None):
        report={'status':status,'seed':SEED,'python':sys.version,'platform':platform.platform(),
                'groups':self.rows,'accepted_receipts':len(self.records),
                'rejected_receipts':len(self.mutations),
                'elapsed_seconds':time.perf_counter()-self.start,
                'lean_status':'NOT_RUN','head_to_head_lean_benchmark':'NOT_RUN',
                'exception':exception}
        (self.out/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
        with (self.out/'certificates.jsonl').open('w') as f:
            for r in self.records:f.write(json.dumps(r,separators=(',',':'))+'\n')
        with (self.out/'rejections.jsonl').open('w') as f:
            for r in self.mutations:f.write(json.dumps(r,separators=(',',':'))+'\n')
        (self.out/'environment.txt').write_text(sys.version+'\n'+platform.platform()+'\n')
        return report


def main():
    if sys.flags.optimize:
        raise SystemExit('Run without -O: experiment assertions must remain enabled.')
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,default=Path('reproduced-results')/
                    datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    args=ap.parse_args()
    r=Run(args.out)
    try:
        r.predecessor_tests();r.petri_tests();r.scalar_tests();r.coupled_tests()
        r.critical_and_algebraic();r.mutation_tests()
    except Exception:
        failure=traceback.format_exc()
        r.write('FAILED',failure)
        (args.out/'failure.txt').write_text(failure)
        raise
    result=r.write('PASSED')
    print(json.dumps({k:v for k,v in result.items() if k!='groups'},indent=2))

if __name__=='__main__':main()
