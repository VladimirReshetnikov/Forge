#!/usr/bin/env python3
"""Separate guarded-program corpus: endpoint equivalence, NOT trace equivalence."""
import argparse, json, random
from pathlib import Path
from forge_resources.examples import problem
from forge_resources.model import Net, RunDAG
from forge_resources.producer import compare_programs
from forge_resources.checker import check_equivalence
from experiments import walk_raw


def main(out):
    out.mkdir(parents=True, exist_ok=True)
    rng=random.Random(20260916)
    records=[]; equal=different=queries=0
    for n in range(120):
        d=1+n%3
        p=problem(d, [(f't{i}',[rng.randrange(3) for _ in range(d)],
                        [rng.randrange(3) for _ in range(d)]) for i in range(3)], [])
        net=Net.from_dict(p)
        left=tuple(rng.randrange(3) for _ in range(rng.randrange(9)))
        right=left if n%2==0 else tuple(rng.randrange(3) for _ in range(rng.randrange(9)))
        def program(word, split=False):
            dag=RunDAG(net)
            if split:
                cut=len(word)//2; root=dag.seq(dag.word(word[:cut]),dag.word(word[cut:]))
            else: root=dag.word(word)
            nodes,roots=dag.compact([root]);return {'nodes':nodes,'root':roots[0]}
        q={'problem':p,'left':program(left),'right':program(right,True)}
        c=compare_programs(q);check_equivalence(q,c)
        if c['verdict']=='equivalent':
            equal+=1
            for _ in range(20):
                m=tuple(rng.randrange(20) for _ in range(d))
                assert walk_raw(p,m,left)==walk_raw(p,m,right)
                queries+=1
        else:
            different+=1;m=tuple(c['separating_initial'])
            assert walk_raw(p,m,left)!=walk_raw(p,m,right)
            queries+=1
        records.append({'name':f'guarded_programs_{n:03}', 'expected':q,'certificate':c})
    # Very large identity comparison is summarized, not concretely expanded.
    p=problem(1,[('unit',[0],[1]),('block',[0],[10**100])],[]);net=Net.from_dict(p)
    dag=RunDAG(net);root=dag.repeat(dag.step(0),10**100);nodes,roots=dag.compact([root]);left={'nodes':nodes,'root':roots[0]}
    dag=RunDAG(net);root=dag.step(1);nodes,roots=dag.compact([root]);right={'nodes':nodes,'root':roots[0]}
    q={'problem':p,'left':left,'right':right};c=compare_programs(q);check_equivalence(q,c)
    assert c['verdict']=='equivalent'
    records.append({'name':'huge_loop_vs_one_block', 'expected':q,'certificate':c})
    (out/'equivalences.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in records))
    summary={'seed':20260916,'random_program_pairs':120,'equivalent':equal,'different':different,
             'concrete_queries':queries,'disagreements':0,'extra_huge_symbolic_pair':1,'records':len(records),
             'meaning':'endpoint partial-function equivalence, ignoring trace and step count'}
    (out/'equivalence-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=Path('reproduced-results'))
    main(parser.parse_args().out)
