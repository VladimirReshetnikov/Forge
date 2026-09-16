"""Test direct closure separation against the eager producer on identical models."""
from __future__ import annotations
import argparse, copy, json, math, subprocess, sys, time
from pathlib import Path
import checker as ck
import search as pr
from run_tests import dump, resource, R, S, ROOT

def run(source, output):
    corpus=ck.load_json(str(source/'corpus.json'))
    rows=[];replays=[]
    for case in corpus:
        p=case['problem'];start=time.perf_counter();r=pr.solve_separation(p)
        assert r['status']=='complete',(case['name'],r)
        search_seconds=time.perf_counter()-start
        c=r['certificate'];start=time.perf_counter();info=ck.verify(p,c)
        replay_seconds=time.perf_counter()-start
        left=[c['nodes'][i]['state'] for i in c['basis']]
        old=case['certificate'];right=[old['nodes'][i]['state'] for i in old['basis']]
        assert left==right,(case['name'],left,right)
        replays.append({'name':case['name'],'problem':p,'certificate':c})
        rows.append({'name':case['name'],'same_exact_basis':True,
            'search_seconds':search_seconds,'replay_seconds':replay_seconds,
            'stats':r['stats'],'checked':info})
    # A small existing global cone subsumes a combinatorially huge local preimage.
    large=[]
    for d,threshold in [(4,20),(6,60),(8,100)]:
        eye=[[int(i==j) for j in range(d)] for i in range(d)]
        dense=[[1]*d]+[[0]*d for _ in range(d-1)]
        consume=[1]+[0]*(d-1);out=[threshold]+[0]*(d-1)
        p=resource(d,2,[R(0,1,consume,eye,out),R(0,1,consume,dense,[0]*d)],[S(1,*out)])
        eager=pr.solve(p,pr.Budget(max_grid=100000))
        r=pr.solve_separation(p,pr.Budget(max_grid=1))
        assert r['status']=='complete',r
        c=r['certificate'];ck.verify(p,c)
        basis=[c['nodes'][i]['state'] for i in c['basis']]
        assert basis==[S(0,*consume),S(1,*out)]
        record={'dimension':d,'threshold':threshold,
            'local_clipping_grid':(threshold+1)**d,
            'local_minimal_predecessors':math.comb(threshold+d-1,d-1),
            'eager_status':eager['status'],'eager_reason':eager.get('reason'),
            'separation_status':r['status'],'separation_stats':r['stats'],
            'certificate_bytes':len(pr.canonical(c).encode())}
        large.append(record)
        dump(output/f'dense-{d}.problem.json',p);dump(output/f'dense-{d}.certificate.json',c)
        replays.append({'name':f'dense_{d}','problem':p,'certificate':c})
    mutations=[]
    case=next(c for c in replays if any(e['predecessor']['kind']=='resource-cover'
                                       for e in c['certificate']['closure']))
    p,c=case['problem'],case['certificate']
    pos=next(i for i,e in enumerate(c['closure']) if e['predecessor']['kind']=='resource-cover')
    for name,change in [
        ('invalid_global_cover',lambda e:e['predecessor'].update(tree=['basis',len(c['basis'])])),
        ('wrong_empty_local_cover',lambda e:e.update(cover=[0])),
        ('bad_direct_split',lambda e:e['predecessor'].update(tree=['split',0,10**20,['basis',0],['basis',0]])),
        ('false_direct_infeasible',lambda e:e['predecessor'].update(tree=['impossible',0])),
        ('missing_direct_row',None)]:
        v=copy.deepcopy(c)
        if change is None:v['closure'].pop(pos)
        else:change(v['closure'][pos])
        try:ck.verify(p,v)
        except ck.Reject as ex:mutations.append({'name':name,'rejected':True,'diagnostic':str(ex)})
        else:raise AssertionError(name)
    # Replay in a fresh process, search imports denied, site packages disabled.
    dump(output/'corpus.json',replays)
    program='''import sys,importlib.abc\nclass Block(importlib.abc.MetaPathFinder):\n def find_spec(self,name,path=None,target=None):\n  if name in ("search","sympy","numpy","scipy"):raise RuntimeError(name)\nsys.meta_path.insert(0,Block())\nsys.path.insert(0,sys.argv[1])\nimport checker\nfor row in checker.load_json(sys.argv[2]):checker.verify(row["problem"],row["certificate"])\nprint("SEPARATION_REPLAY_OK")'''
    result=subprocess.run([sys.executable,'-S','-c',program,str(ROOT/'prototype'),str(output/'corpus.json')],text=True,capture_output=True)
    assert result.returncode==0,result.stderr
    summary={'same_models':len(corpus),'identical_bases':len(rows),'mismatches':0,
        'dense_preimage_fixtures':large,'mutations':mutations,
        'independent_replay':{'certificates':len(replays),'returncode':result.returncode,'stdout':result.stdout,
            'search_import_forbidden':True,'site_packages_disabled':True},
        'interpretation':'An ablation of two delivered Python producers on identical models, not a Lean tactic comparison.'}
    dump(output/'measurements.json',rows);dump(output/'summary.json',summary)
    print(json.dumps(summary,indent=2))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path,default=ROOT/'results')
    ap.add_argument('--output',type=Path,default=ROOT/'reproduced-separation')
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    try:run(a.source.resolve(),a.output.resolve())
    except Exception:
        import traceback
        (a.output/'FAILED_RUN.txt').write_text(traceback.format_exc());raise
if __name__=='__main__':main()
