"""Deterministic experiment suite. Writes to a NEW results directory by default.
Stored counts use distinct units and are not summed into a spurious success rate.
"""
from __future__ import annotations
import argparse
from collections import Counter
from copy import deepcopy
import csv
import json
import platform
import random
import sys
import time
from pathlib import Path
from formula import *
from producer import Compiler, Limits, BudgetExceeded, accepts, extract_witness
from checker import verify, check_witness, Rejected

SEED = 20260915

def named_queries():
    E = eq
    L = le
    yield 'successor_total', [], Forall('x', Exists('y', E({'y':1,'x':-2},1))), True
    yield 'no_greatest_natural', [], neg(Exists('y', Forall('x', L({'x':1,'y':-1})))), True
    yield 'uniform_upper_bound_false', [], Exists('y', Forall('x', L({'x':1,'y':-1}))), False
    yield 'successor_cut', [], Forall('x', Exists('y', Forall('z', Iff(L({'z':1,'x':-1}),L({'z':1,'y':-1},-1))))), True
    yield 'half_cut', [], Forall('x', Exists('y', Forall('z', Iff(L({'z':2,'x':-1}),L({'z':1,'y':-1},-1))))), True
    for m in (3,7,17):
        f=Forall('n',Exists('q',Exists('r',And(E({'n':1,'q':-m,'r':-1}),L({'r':1},m-1)))))
        yield f'division_{m}', [], f, True
    yield 'residue_unbounded', [], Forall('x',Exists('y',And(L({'x':1,'y':-1},-1),cong({'y':1},3,5)))), True
    yield 'negative_coefficients', ['x','y'], Iff(L({'x':-3,'y':2},-7),neg(L({'x':3,'y':-2},6))), True
    yield 'congruence_translation', ['x','y'], Implies(E({'y':1,'x':-1},21),Iff(cong({'x':1},2,7),cong({'y':1},2,7))), True
    r=Exists('a',Exists('b',E({'n':1,'a':-5,'b':-7})))
    yield 'coin_5_7_threshold_24', ['n'], Implies(L({'n':-1},-24),r), True
    yield 'coin_5_7_threshold_23_false', ['n'], Implies(L({'n':-1},-23),r), False
    yield 'powers_two_unbounded', [], Forall('x',Exists('y',And(pow2('y'),L({'x':1,'y':-1},-1)))), True
    yield 'all_naturals_powers_false', ['x'], pow2('x'), False
    yield 'odd_power_is_one', ['x'], Implies(And(pow2('x'),cong({'x':1},1,2)),E({'x':1},1)), True
    yield 'thue_morse_even', ['x','y'], Implies(E({'y':1,'x':-2}),Iff(parity('y'),parity('x'))), True
    yield 'thue_morse_odd', ['x','y'], Implies(E({'y':1,'x':-2},1),Iff(parity('y'),neg(parity('x')))), True
    yield 'thue_morse_alternating_false', ['x','y'], Implies(E({'y':1,'x':-1},1),Iff(parity('y'),neg(parity('x')))), False
    yield 'even_popcount_unbounded', [], Forall('x',Exists('y',And(L({'x':1,'y':-1},-1),parity('y')))), True
    yield 'same_popcount_parity_later', [], Forall('x',Exists('y',And(L({'x':1,'y':-1},-1),Iff(parity('x'),parity('y'))))), True
    yield 'bitand_commutes', ['x','y','z'], Iff(bitand('x','y','z'),bitand('y','x','z')), True
    yield 'xor_recovery', ['x','y','z'], Implies(bitxor('x','y','z'),bitxor('x','z','y')), True
    parity_law=Iff(parity('s'),Iff(parity('x'),parity('y')))
    assumptions=And(And(bitand('x','y','z'),E({'z':1})),E({'x':1,'y':1,'s':-1}))
    yield 'carry_free_parity_addition', ['x','y','z','s'], Implies(assumptions,parity_law), True
    yield 'unrestricted_parity_addition_false', ['x','y','s'], Implies(E({'x':1,'y':1,'s':-1}),parity_law), False


def clone(x):
    return json.loads(json.dumps(x))


def rejected(b, query):
    try:
        verify(b, query)
    except Rejected:
        return True
    return False


def run(out: Path):
    out.mkdir(parents=True, exist_ok=True)
    certdir=out/'certificates'; querydir=out/'queries'
    certdir.mkdir(exist_ok=True); querydir.mkdir(exist_ok=True)
    rng=random.Random(SEED)
    summary={'seed':SEED,'python':sys.version,'platform':platform.platform(),
             'lean_status':'NOT_RUN: no Lean executable was available',
             'comparison_with_lean_tactics':'NOT_RUN'}
    named=[]; bundles=[]; mutation_counts=Counter(); mutations=[]
    def save(name,ctx,f,b):
        (querydir/(name+'.json')).write_text(json.dumps({'context':ctx,'formula':f},indent=2)+'\n')
        (certdir/(name+'.json')).write_text(json.dumps(b,separators=(',',':'))+'\n')
    for name,ctx,f,expected in named_queries():
        start=time.perf_counter(); compiler=Compiler(); b=compiler.bundle(f,ctx)
        gen=time.perf_counter()-start
        start=time.perf_counter(); stats=verify(b,b['query']); replay=time.perf_counter()-start
        actual=b['verdict']['kind']=='valid'
        assert actual==expected,(name,expected,b['verdict'])
        named.append({'name':name,'expected_universal_truth':expected,
                      **stats,'produce_seconds':gen,'replay_seconds':replay,
                      'certificate_bytes':len(json.dumps(b,separators=(',',':'))),
                      'counterexample':b['verdict'].get('values')})
        save(name,ctx,f,b); bundles.append((name,b))
        for i,node in enumerate(b['nodes']):
            c=clone(b); c['nodes'][i]['dfa']['final'][0]=not c['nodes'][i]['dfa']['final'][0]
            assert rejected(c,b['query']),('final mutation escaped',name,i)
            mutation_counts['flip_acceptance']+=1
            n=len(node['dfa']['trans'])
            if n>1:
                c=clone(b); c['nodes'][i]['dfa']['trans'][0][0]=(c['nodes'][i]['dfa']['trans'][0][0]+1)%n
                assert rejected(c,b['query']),('transition mutation escaped',name,i)
                mutation_counts['change_transition']+=1
            if node['kind']=='exists':
                c=clone(b)
                ranks=c['nodes'][i]['tail_rank']; j=next((j for j,r in enumerate(ranks) if r is not None),None)
                if j is not None:
                    ranks[j]=len(ranks)
                    assert rejected(c,b['query'])
                    mutation_counts['out_of_range_tail_rank']+=1
        c=clone(b); c['root']=len(c['nodes']); assert rejected(c,b['query']); mutation_counts['bad_root']+=1
        q=clone(b['query']); q['formula']=neg(q['formula']); assert rejected(b,q); mutation_counts['wrong_query']+=1
    (out/'named_results.json').write_text(json.dumps(named,indent=2)+'\n')
    summary['named_queries']={'count':len(named),'valid':sum(r['verdict']=='valid' for r in named),
                              'counterexamples':sum(r['verdict']=='counterexample' for r in named)}
    # Quantifier-free differential oracle: ordinary Python integer arithmetic.
    valuations=0; automata=0; padding_checks=0; diff_records=[]
    for t in range(180):
        coeff={'x':rng.randint(-6,6),'y':rng.randint(-6,6)}; rhs=rng.randint(-16,16)
        op=t%6
        if op==0:
            f=eq(coeff,rhs); oracle=lambda x,y:coeff['x']*x+coeff['y']*y==rhs
        elif op==1:
            f=le(coeff,rhs); oracle=lambda x,y:coeff['x']*x+coeff['y']*y<=rhs
        elif op==2:
            m=rng.randint(1,13); f=cong(coeff,rhs,m); oracle=lambda x,y:(coeff['x']*x+coeff['y']*y-rhs)%m==0
        elif op==3:
            p=t%2; f=Iff(parity('x',p),parity('y')); oracle=lambda x,y:(x.bit_count()%2==p)==(y.bit_count()%2==0)
        elif op==4:
            f=And(pow2('x'),le(coeff,rhs)); oracle=lambda x,y:x>0 and (x&(x-1))==0 and coeff['x']*x+coeff['y']*y<=rhs
        else:
            f=Or(eq(coeff,rhs),neg(le(coeff,rhs+3))); oracle=lambda x,y:coeff['x']*x+coeff['y']*y==rhs or coeff['x']*x+coeff['y']*y>rhs+3
        c=Compiler(); b=c.bundle(f,['x','y']); verify(b,b['query']); d=c.nodes[b['root']]['dfa']; automata+=1
        for x in range(16):
            for y in range(16):
                expected=bool(oracle(x,y)); assert accepts(d,[x,y])==expected,(t,x,y)
                valuations+=1
                for pad in (1,3):
                    assert accepts(d,[x,y],pad)==expected,(t,x,y,pad)
                    padding_checks+=1
        diff_records.append({'case':t,'query':b['query'],'root_states':len(d['trans'])})
    (out/'differential_cases.json').write_text(json.dumps(diff_records,indent=2)+'\n')
    summary['quantifier_free_differential']={'automata':automata,'valuations':valuations,'additional_padding_evaluations':padding_checks}
    # Truly independent finite oracle for guarded, alternating quantifiers.
    guarded=[]; oracle_leaves=0
    for t in range(60):
        B=2+t%4; cs={v:rng.randint(-4,4) for v in ('x','y','z')}; rhs=rng.randint(-7,7)
        f0=le(cs,rhs) if t%2==0 else cong(cs,rhs,2+t%5)
        if t%3==0: f0=Iff(f0,parity('y'))
        def local(x,y,z):
            val=sum(cs[v]*n for v,n in zip(('x','y','z'),(x,y,z)))
            p=(val<=rhs) if t%2==0 else ((val-rhs)%(2+t%5)==0)
            return p==(y.bit_count()%2==0) if t%3==0 else p
        table=[[[local(x,y,z) for z in range(B+1)] for y in range(B+1)] for x in range(B+1)]
        oracle_leaves+=(B+1)**3
        expected=all(any(all(row) for row in slab) for slab in table)
        f=Forall('x',Implies(le({'x':1},B),Exists('y',And(le({'y':1},B),Forall('z',Implies(le({'z':1},B),f0))))))
        c=Compiler(); b=c.bundle(f,[]); stats=verify(b,b['query']); actual=b['verdict']['kind']=='valid'
        assert actual==expected,('guarded',t,expected,b['verdict'])
        name=f'guarded_{t:02d}'; save(name,[],f,b)
        guarded.append({'case':t,'bound':B,'expected':expected,**stats})
    (out/'guarded_results.json').write_text(json.dumps(guarded,indent=2)+'\n')
    summary['guarded_alternation']={'formulas':len(guarded),'complete_oracle_leaf_evaluations':oracle_leaves,
                                  'true':sum(r['expected'] for r in guarded),'false':sum(not r['expected'] for r in guarded)}
    # Canonical witness graphs, including a non-Presburger selector.
    witnesses=[]; witness_sources=[]
    rels=[('double_successor',eq({'y':1,'x':-2},1),lambda x:2*x+1),
          ('quotient_seven',Exists('r',And(eq({'x':1,'y':-7,'r':-1}),le({'r':1},6))),lambda x:x//7),
          ('next_power_two',And(pow2('y'),le({'x':1,'y':-1},-1)),lambda x:1<<x.bit_length()),
          ('next_same_parity',And(le({'x':1,'y':-1},-1),Iff(parity('x'),parity('y'))),None),
          ('least_coin_five_count',Exists('b',eq({'x':1,'y':-5,'b':-7})),None)]
    minimality_observations=0; large_witnesses=0; no_witnesses=0
    for name,r,oracle in rels:
        g=least_graph(r,'y','u'); c=Compiler(); b=c.bundle(g,['x','y']); verify(b,b['query']); save('witness_'+name,['x','y'],g,b)
        d=c.nodes[b['root']]['dfa']; witness_sources.append({'name':name,'states':len(d['trans']),'nodes':len(c.nodes)})
        for x in list(range(128))+[2**64-1,2**128+3,10**100+37]:
            record=extract_witness(d,[x])
            if name=='next_same_parity':
                expected=x+1
                while expected.bit_count()%2!=x.bit_count()%2: expected+=1
            elif name=='least_coin_five_count':
                a=(3*x)%7; expected=a if 5*a<=x else None
            else: expected=oracle(x)
            if expected is None:
                assert record is None; no_witnesses+=1
                continue
            assert record is not None and record['witness']==expected,(name,x,record,expected)
            check_witness(d,[x],record)
            if x<128:
                # Direct source arithmetic/bit oracles, not the compiled graph.
                for smaller in range(expected):
                    if name=='double_successor': ok=smaller==2*x+1
                    elif name=='quotient_seven': ok=0<=x-7*smaller<=6
                    elif name=='next_power_two': ok=smaller>x and smaller>0 and (smaller&(smaller-1))==0
                    elif name=='next_same_parity': ok=smaller>x and smaller.bit_count()%2==x.bit_count()%2
                    else: ok=x-5*smaller>=0 and (x-5*smaller)%7==0
                    assert not ok
                    minimality_observations+=1
            else: large_witnesses+=1
            witnesses.append({'source':'witness_'+name,'record':record})
            changed=clone(record); changed['witness']+=1
            try: check_witness(d,[x],changed)
            except Rejected: mutation_counts['witness_value']+=1
            else: raise AssertionError('bad witness escaped')
    (out/'witnesses.json').write_text(json.dumps(witnesses,separators=(',',':'))+'\n')
    (out/'witness_sources.json').write_text(json.dumps(witness_sources,indent=2)+'\n')
    summary['witnesses']={'graphs':len(rels),'accepted_records':len(witnesses),'absence_results':no_witnesses,
                          'large_input_records':large_witnesses,'smaller_value_oracle_checks':minimality_observations}
    # The broken same-length projection: an intentional negative control.
    c=Compiler(); idx=c.compile(eq({'y':1,'x':-2},1),['x','y']); source=c.nodes[idx]['dfa']
    def step(states,a): return tuple(sorted({source['trans'][q][a|(bit<<1)] for q in states for bit in (0,1)}))
    naive,_=c.explore(1,(source['start'],),step,lambda ss:any(source['final'][q] for q in ss))
    actual=Compiler(); cert=actual.bundle(Exists('y',eq({'y':1,'x':-2},1)),['x']); corrected=actual.nodes[cert['root']]['dfa']
    regressions=[]
    for x in [0,1,3,7,15,31,1023,2**128-1]:
        row={'x':x,'naive_minimal_encoding':accepts(naive,[x]),'naive_one_zero_padding':accepts(naive,[x],1),'corrected':accepts(corrected,[x])}
        assert not row['naive_minimal_encoding'] and row['naive_one_zero_padding'] and row['corrected']
        regressions.append(row)
    (out/'padding_regressions.json').write_text(json.dumps(regressions,indent=2)+'\n')
    summary['padding_regression']={'failing_naive_cases':len(regressions),'corrected_cases':len(regressions)}
    # Strict malformed-input tests, including bool/int equality confusion.
    base=bundles[0][1]
    c=clone(base); atomnode=next(n for n in c['nodes'] if n['kind']=='atom'); atomnode['formula']['rhs']=True
    assert rejected(c,base['query']); mutation_counts['boolean_for_integer']+=1
    c=clone(base); atomnode=next(n for n in c['nodes'] if n['kind']=='atom'); atomnode['formula']['rhs']=1.0
    assert rejected(c,base['query']); mutation_counts['float_for_integer']+=1
    c=clone(base); c['nodes'][0]['dfa']['trans'][0].pop(); assert rejected(c,base['query']); mutation_counts['incomplete_dfa']+=1
    c=clone(base); c['nodes'][0]['dfa']['trans'][0][0]=-1; assert rejected(c,base['query']); mutation_counts['negative_index']+=1
    c=clone(base); c['nodes'][-1]['child']=len(c['nodes']); assert rejected(c,base['query']); mutation_counts['cyclic_dependency']+=1
    c=clone(base); c['status']='unknown'; assert rejected(c,base['query']); mutation_counts['unknown_as_proof']+=1
    # Missing and spurious tail members must both be rejected.
    for tag,mutate in [('missing_tail',False),('spurious_tail',True)]:
        found=False
        for name,b in bundles:
            for i,node in enumerate(b['nodes']):
                if node['kind']!='exists': continue
                ranks=node['tail_rank']
                js=[j for j,r in enumerate(ranks) if (r is None if mutate else r==0)]
                if not js: continue
                c=clone(b); j=js[0]
                c['nodes'][i]['tail_rank'][j]=0 if mutate else None
                c['nodes'][i]['tail_choice'][j]=None
                assert rejected(c,b['query']),(tag,name,i)
                mutation_counts[tag]+=1; found=True; break
            if found: break
        assert found,tag
    # Operational limit is UNKNOWN, never false.
    limited=0
    for lim in [Limits(max_states=1),Limits(max_tracks=0),Limits(max_nodes=1),Limits(max_cells=1)]:
        try: Compiler(lim).bundle(neg(eq({'x':1,'y':-2},1)),['x','y'])
        except BudgetExceeded: limited+=1
        else: raise AssertionError('budget did not trigger')
    summary['budget_controls']={'unknown_outcomes':limited}
    summary['mutation_rejections']={**mutation_counts,'total':sum(mutation_counts.values())}
    # Ablation uses identical queries, not a comparison with a Lean tactic.
    ablation=[]
    for name,ctx,f,expected in list(named_queries())[:9]:
        for minimize in (False,True):
            start=time.perf_counter(); c=Compiler(minimize=minimize); b=c.bundle(f,ctx); duration=time.perf_counter()-start
            stats=verify(b,b['query']); assert (stats['verdict']=='valid')==expected
            ablation.append({'name':name,'minimize':minimize,**stats,'produce_seconds':duration})
    (out/'ablation.json').write_text(json.dumps(ablation,indent=2)+'\n')
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--out',type=Path,default=Path('reproduced-results'))
    args=p.parse_args(); run(args.out)
