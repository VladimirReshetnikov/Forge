#!/usr/bin/env python3
"""Write results to a NEW directory (default: reproduced-results)."""
import argparse,copy,json,platform,sys,time
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
from corpus import positives,systems,false_cases,true_outside,roots
from forge_flow.search import canonical_search,ladder_search,ordered_search,system_search,optimal_ladder
from forge_flow.check import check_ladder,check_system,check_obstruction,check_minimality
from forge_flow.witness_search import root,refute
from forge_flow.enclosure import check_root,check_refutation


def write_json(p,data): p.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',default='reproduced-results')
    args=ap.parse_args();out=Path(args.out);out.mkdir(parents=True,exist_ok=False)
    records=[];t0=time.perf_counter();failures=[]
    ablation=Counter();mutations=Counter();stats=Counter()
    try:
        for name,f in positives():
            t=time.perf_counter();canonical=canonical_search(f);ct=time.perf_counter()-t
            t=time.perf_counter();short=ladder_search(f);bt=time.perf_counter()-t
            if canonical['status']!='certificate' or short['status']!='certificate':
                raise AssertionError((name,canonical,short))
            t=time.perf_counter();optimal=optimal_ladder(f);ot=time.perf_counter()-t
            assert optimal['status']=='certificate'
            assert optimal['steps']==len(short['certificate']['cofactors'])
            c=optimal['certificate'];assert check_ladder(f.problem(),c)
            assert check_minimality(f.problem(),c,optimal['minimality'])
            assert check_ladder(f.problem(),canonical['certificate'])
            ablation['cases']+=1
            ablation['increasing_order_accepted']+=1
            ablation['decreasing_order_accepted']+=bool(ordered_search(f,True))
            ablation['shorter_than_increasing']+=len(c['cofactors'])<canonical['steps']
            ablation['increasing_steps']+=canonical['steps'];ablation['compressed_steps']+=len(c['cofactors'])
            stats['positive_certificates']+=1
            records.append({'id':name,'lane':'positive','problem':f.problem(),'certificate':c,
                            'canonical_steps':canonical['steps'],'compressed_steps':len(c['cofactors']),
                            'canonical_seconds':ct,'optimal_seconds':ot,'bfs_seconds':bt,'bfs_states':short['visited'],
                            'minimality':optimal['minimality'],'feasibility_checks':optimal['feasibility_checks']})
            for i in range(len(c['anchors'])):
                bad=copy.deepcopy(c);bad['anchors'][i][0]+=bad['anchors'][i][1]
                mutations['ladder_anchor_attempts']+=1
                mutations['ladder_anchor_rejected']+=not check_ladder(f.problem(),bad)
        for name,r,H in systems():
            x=system_search(H,diagonal=(-2*r,-r,F(0),r,2*r),off_diagonal=(F(0),r,2*r))
            assert x['status']=='certificate',(name,x)
            c=x['certificate'];p=[h.problem() for h in H];assert check_system(p,c)
            records.append({'id':name,'lane':'system','problems':p,'certificate':c})
            stats['system_certificates']+=1
            for i in range(len(H)):
                bad=copy.deepcopy(c);bad['anchors'][i][0]+=bad['anchors'][i][1]
                mutations['system_anchor_attempts']+=1;mutations['system_anchor_rejected']+=not check_system(p,bad)
        for name,f in false_cases():
            a=canonical_search(f);assert a['status']=='no_ladder';assert check_obstruction(f.problem(),a['certificate'])
            x=refute(f);assert x['status']=='certificate',(name,x)
            c=x['certificate'];assert check_refutation(f.problem(),c)
            records.append({'id':name,'lane':'negative_point','problem':f.problem(),'certificate':c,
                            'grammar_obstruction':a['certificate']});stats['negative_point_certificates']+=1
            bad=copy.deepcopy(c);bad['enclosure'][1][0]+=bad['enclosure'][1][1]
            mutations['point_bound_attempts']+=1;mutations['point_bound_rejected']+=not check_refutation(f.problem(),bad)
        for name,f in true_outside():
            a=canonical_search(f);assert a['status']=='no_ladder';assert check_obstruction(f.problem(),a['certificate'])
            assert refute(f)['status']=='unknown'
            records.append({'id':name,'lane':'grammar_obstruction','problem':f.problem(),'certificate':a['certificate']})
            stats['true_outside_grammar']+=1
        for name,f,a,b in roots():
            x=root(f,a,b);assert x['status']=='certificate',(name,x)
            assert check_root(x['problem'],x['certificate'])
            records.append({'id':name,'lane':'root','problem':x['problem'],'certificate':x['certificate']})
            stats['root_certificates']+=1
            bad=copy.deepcopy(x['certificate']);bad['direction']*=-1
            mutations['root_direction_attempts']+=1;mutations['root_direction_rejected']+=not check_root(x['problem'],bad)
        for k,v in list(mutations.items()):
            if k.endswith('_attempts'): assert v==mutations[k.replace('_attempts','_rejected')]
    except Exception as e:
        failures.append(repr(e));raise
    finally:
        write_json(out/'certificates.json',records)
        write_json(out/'summary.json',{'python':sys.version,'platform':platform.platform(),
            'elapsed_seconds':time.perf_counter()-t0,'counts':dict(stats),'ablation':dict(ablation),
            'mutations':dict(mutations),'failures':failures,'lean':'NOT_RUN',
            'comparison_to_lean_tactics':'NOT_RUN','arithmetic':'fractions.Fraction; no floats in decisions'})
    print(json.dumps({'counts':dict(stats),'ablation':dict(ablation),'mutations':dict(mutations)},indent=2))

if __name__=='__main__':main()
