"""Produce exact, seeded differential results. Output never overwrites source evidence by default."""
from __future__ import annotations
from collections import Counter
from copy import deepcopy
from pathlib import Path
import argparse,json,platform,random,sys,time
import antichain,checker,fixtures,mixed,nominal,oracles


def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,default=Path('reproduced-results'))
    ap.add_argument('--seed',type=int,default=20260915)
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    rng=random.Random(args.seed);corpus=[];families={};mutations=[]
    def record(engine,name,problem,cert,oracle=None):
        good=checker.check_vass(problem,cert) if engine=='vass' else (
             checker.check_mixed(problem,cert) if engine=='mixed' else checker.check_nominal(*problem,cert))
        if cert['kind']=='unknown':
            assert not good
        else:
            assert good,(engine,name,cert)
        corpus.append({'engine':engine,'name':name,'problem':problem,'certificate':cert,'oracle':oracle})

    examples={}
    for name,p in [('mutex',fixtures.mutex()),('mutex_bug',fixtures.mutex(True)),('axes',fixtures.axes()),
                   ('delayed_101',fixtures.delayed()),('enabling',fixtures.enabling_trap())]:
        checker.validate_vass(p);c=antichain.solve(p);record('vass',name,p,c);examples[name]=c
    for name,a,b in [('lru_register_swap',fixtures.lru(),fixtures.permute_registers(fixtures.lru(),[1,0])),
                     ('lru_fifo',fixtures.lru(),fixtures.lru(True)),
                     ('eviction_register_swap',fixtures.lru(atom_output=True),
                      fixtures.permute_registers(fixtures.lru(atom_output=True),[1,0]))]:
        checker.validate_machine(a);checker.validate_machine(b)
        c=nominal.equivalence(a,b);o=oracles.finite_nominal(a,b);record('nominal',name,[a,b],c,o);examples[name]=c
    examples['lru_fifo_two_keys']=oracles.finite_nominal(fixtures.lru(),fixtures.lru(True),2)
    for name,p in [('owner_pool',fixtures.owner_pool()),('owner_pool_bug',fixtures.owner_pool(True))]:
        checker.validate_register_net(p);c=mixed.solve(p);record('mixed',name,p,c);examples[name]=c

    start=time.perf_counter();outcomes=Counter();oracle_states=0
    for i in range(300):
        p=fixtures.random_vass(rng);checker.validate_vass(p)
        c=antichain.solve(p);o=oracles.finite_vass(p)
        assert c['kind']!='unknown',(i,c)
        assert (c['kind']=='safe') == o['safe'],(i,p,c,o)
        outcomes[c['kind']]+=1;oracle_states+=o['states'];record('vass',f'random_{i:03d}',p,c,o)
    families['vass']={'cases':300,'outcomes':dict(outcomes),'oracle_agreements':300,
                      'oracle_state_visits':oracle_states,'seconds':time.perf_counter()-start}

    start=time.perf_counter();outcomes=Counter();oracle_states=0;shortest=0;orbit_total=0
    for i in range(160):
        a=fixtures.random_machine(rng)
        perm=list(range(a['registers']));rng.shuffle(perm)
        b=fixtures.permute_registers(a,perm)
        if i%2:
            j=rng.randrange(len(b['rules']))
            typ,e=b['rules'][j]['output']
            b['rules'][j]['output']=['bool',['not',e]] if typ=='bool' else ['atom',['input']]
        checker.validate_machine(a);checker.validate_machine(b)
        c=nominal.equivalence(a,b);o=oracles.finite_nominal(a,b)
        assert c['kind']!='unknown',(i,c)
        assert (c['kind']=='equivalent') == o['equivalent'],(i,a,b,c,o)
        if c['kind']=='different':
            assert len(c['word'])==o['shortest_length'],(i,c,o)
            shortest+=1
        outcomes[c['kind']]+=1;oracle_states+=o['states'];orbit_total+=c['stats']['orbits']
        record('nominal',f'random_{i:03d}',[a,b],c,o)
    families['nominal']={'cases':160,'outcomes':dict(outcomes),'oracle_agreements':160,
                        'shortest_witness_agreements':shortest,'oracle_state_visits':oracle_states,
                        'orbit_state_visits':orbit_total,'seconds':time.perf_counter()-start}

    start=time.perf_counter();outcomes=Counter();oracle_states=0
    for i in range(180):
        p=fixtures.random_register_net(rng);checker.validate_register_net(p)
        c=mixed.solve(p);o=oracles.finite_mixed(p)
        assert c['kind']!='unknown',(i,c)
        assert (c['kind']=='safe')==o['safe'],(i,p,c,o)
        outcomes[c['kind']]+=1;oracle_states+=o['states'];record('mixed',f'random_{i:03d}',p,c,o)
    families['mixed']={'cases':180,'outcomes':dict(outcomes),'oracle_agreements':180,
                       'oracle_state_visits':oracle_states,'seconds':time.perf_counter()-start}

    # Mutations guaranteed semantically or structurally invalid; do not claim all edits
    # to a valid certificate should be rejected (redundant valid basis vectors are legal).
    for entry in corpus:
        e,p,c=entry['engine'],entry['problem'],entry['certificate']
        cc=deepcopy(c);cc['schema']=99
        check=lambda v: checker.check_vass(p,v) if e=='vass' else (checker.check_mixed(p,v) if e=='mixed' else checker.check_nominal(*p,v))
        assert not check(cc);mutations.append({'engine':e,'name':entry['name'],'mutation':'schema','rejected':True})
        cc=deepcopy(c)
        if e=='vass':
            if cc['kind']=='safe':cc['basis']=[]
            else:cc['initial']=len(p['initials'])
        elif e=='nominal':
            if cc['kind']=='equivalent':cc['states']=[]
            else:cc['word']=[]
        else:
            if cc['kind']=='safe':cc['states']=[]
            else:cc['initial']=len(p['initials'])
        assert not check(cc),(e,entry['name']);mutations.append({'engine':e,'name':entry['name'],'mutation':'required_content','rejected':True})

    summary={'seed':args.seed,'python':sys.version,'platform':platform.platform(),
             'families':families,'handcrafted_examples':10,'stored_objects':len(corpus),
             'rejected_mutations':len(mutations),'examples':examples,
             'lean_status':'NOT_RUN: no Lean/elan executable; compiler plugin search found none',
             'external_solver_dependencies':[],
             'evidence_scope':'Python search, search-independent certificate replay, finite-oracle comparison; not Lean-kernel verification or a tactic comparison.'}
    for name,data in [('summary.json',summary),('corpus.json',corpus),('mutations.json',mutations)]:
        (args.output/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:summary[k] for k in ['seed','families','stored_objects','rejected_mutations']},indent=2))

if __name__=='__main__':main()
