#!/usr/bin/env python3
"""Deterministic, standard-library-only experiments with independent finite oracles.

Writes to a caller-selected directory; recorded results are never overwritten by
an ordinary reproduction command. These are Python experiments, not Lean tests.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
from copy import deepcopy
from itertools import permutations, product
from math import factorial
from pathlib import Path
import json
import platform
import random
import sys
if not __debug__:
    raise RuntimeError("Regression and replay scripts require assertions enabled; do not use -O")
from time import perf_counter
from forge_symmetry.producer import (
    build_chain, named_problem, canonical_certificate,
    canonical_family_certificate, burnside_certificate, SearchLimit,
)
from forge_symmetry.checker import (
    verify_chain, verify_canonical, verify_canonical_family, verify_burnside,
    verify_family, verify_cnf_symmetry, InvalidCertificate, CheckLimit, load_json,
)


def group_oracle(problem: dict) -> set[tuple[int, ...]]:
    """Right Cayley-graph traversal, separate from producer's left traversal."""
    n = problem['degree']
    identity = tuple(range(n))
    result = {identity}
    todo = deque([identity])
    while todo:
        p = todo.popleft()
        for g in problem['generators']:
            nxt = tuple(p[g[j]] for j in range(n))
            if nxt not in result:
                result.add(nxt)
                todo.append(nxt)
    return result


def coloring_orbits(problem: dict, q: int) -> list[tuple[int, ...]]:
    """Connected components of the assignment graph; no Burnside calculation."""
    n = problem['degree']
    unseen = set(product(range(q), repeat=n))
    representatives = []
    while unseen:
        source = min(unseen)
        representatives.append(source)
        unseen.remove(source)
        todo = deque([source])
        while todo:
            c = todo.popleft()
            for g in problem['generators']:
                out = [0] * n
                for i in range(n):
                    out[g[i]] = c[i]
                nxt = tuple(out)
                if nxt in unseen:
                    unseen.remove(nxt)
                    todo.append(nxt)
    return representatives


def oracle_image(g: tuple[int, ...], colors: list[int]) -> tuple[int, ...]:
    return tuple(colors[g.index(i)] for i in range(len(g)))


def run(destination: Path, include_large: bool = True) -> dict:
    destination.mkdir(parents=True, exist_ok=False)
    corpus = destination / 'corpus'
    corpus.mkdir()
    rng = random.Random(20260915)
    counts = Counter()
    metrics = []
    certificates = []
    started = perf_counter()
    problems: list[tuple[str, dict]] = []
    s3 = list(permutations(range(3)))
    for i, a in enumerate(s3):
        for j, b in enumerate(s3):
            problems.append((f'exhaustive-S3-pair-{i}-{j}', {'degree':3,'generators':[list(a),list(b)]}))
    for n in range(2, 8):
        for trial in range(12):
            gens = []
            for _ in range(1 + trial % 3):
                p = list(range(n)); rng.shuffle(p); gens.append(p)
            problems.append((f'random-{n}-{trial}', {'degree':n,'generators':gens}))
    for family in ('S','A','C','D','trivial'):
        for n in range(9):
            problems.append((f'named-{family}-{n}', named_problem(family,n)))

    for name, problem in problems:
        n = problem['degree']
        t0 = perf_counter(); search = build_chain(problem); t1 = perf_counter()
        certificate = search.export(); checked = verify_chain(problem, certificate); t2 = perf_counter()
        group = group_oracle(problem)
        assert checked.order == len(group), name
        counts['chain_instances_checked_against_full_group_oracle'] += 1
        # Exhaustive membership through degree 5; bounded random queries above.
        candidates = list(permutations(range(n))) if n <= 5 else []
        if n > 5:
            for _ in range(120):
                p = list(range(n)); rng.shuffle(p); candidates.append(tuple(p))
            candidates.extend(sorted(group)[:20])
        queries = []
        for p in candidates:
            expected = p in group
            assert checked.contains(p) == expected, (name, p)
            counts['membership_queries'] += 1
            counts['membership_positive' if expected else 'membership_negative'] += 1
            queries.append([list(p), expected])
        bundle = {'name':name, 'problem':problem, 'chain':certificate, 'membership':queries,
                  'canonical':[], 'canonical_family':[]}
        if n <= 7:
            for trial in range(2):
                colors = [rng.randrange(3) for _ in range(n)]
                image, stat = canonical_certificate(search, colors, max_nodes=100_000)
                got = verify_canonical(checked, colors, image)
                expected = min(oracle_image(p, colors) for p in group)
                assert tuple(got['best']) == expected, name
                counts['generic_canonical_queries'] += 1
                counts['generic_canonical_cover_nodes'] += got['nodes']
                bundle['canonical'].append({'colors':colors, 'certificate':image, 'expected':list(expected)})
        family = None
        if checked.order == factorial(n):
            family = 'S'
        elif n >= 2 and 2*checked.order == factorial(n) and all(
                sum(g[i]>g[j] for i in range(n) for j in range(i+1,n))%2 == 0
                for g in problem['generators']):
            family = 'A'
        if family:
            symbolic = {'format':'forge.symmetry.family.v1','family':family}
            vf = verify_family(checked, symbolic)
            bundle['family'] = symbolic
            for colors in ([rng.randrange(3) for _ in range(n)], list(reversed(range(n)))):
                image = canonical_family_certificate(search, list(colors), family)
                got = verify_canonical_family(checked, list(colors), image)
                expected = min(oracle_image(p, list(colors)) for p in group)
                assert tuple(got['best']) == expected
                counts['family_canonical_queries'] += 1
                bundle['canonical_family'].append({'colors':list(colors),'certificate':image,'expected':list(expected)})
        if name.startswith('named-') and n <= 7:
            census = burnside_certificate(problem)
            inventory = verify_burnside(checked, census)
            bundle['burnside'] = census
            bundle['color_counts'] = []
            for q in range(4):
                expected = len(coloring_orbits(problem,q))
                assert inventory.count_colors(q) == expected, (name, q)
                counts['burnside_color_count_queries'] += 1
                bundle['color_counts'].append([q,expected])
                if family:
                    assert vf.count_colors(q) == expected
                    counts['symbolic_family_count_queries'] += 1
            weights = Counter(sum(c) for c in coloring_orbits(problem,2))
            bundle['binary_counts'] = []
            for weight in range(n+2):
                expected = weights[weight]
                assert inventory.count_binary_weight(weight) == expected
                counts['burnside_fixed_weight_queries'] += 1
                bundle['binary_counts'].append([weight,expected])
            counts['cycle_inventories'] += 1
        (corpus / f'{name}.json').write_text(json.dumps(bundle,separators=(',',':'))+'\n')
        certificates.append(name)
        metrics.append({'case':name,'degree':n,'order':checked.order,'strong_generators':len(search.strong),
                        'word_dag_nodes':len(certificate['word_dag']),
                        'transversal_entries':sum(len(t) for t in checked.tables),
                        'schreier_checks':checked.schreier_checks,
                        'search_seconds':t1-t0,'check_seconds':t2-t1,
                        'certificate_bytes':len(json.dumps(certificate,separators=(',',':')).encode())})

    large_metrics = []
    if include_large:
        for family,n in [('S',15),('S',30),('S',40),('A',12),('A',20),('D',50),('C',97)]:
            problem = named_problem(family,n)
            t0=perf_counter(); search=build_chain(problem); t1=perf_counter()
            certificate=search.export(); checked=verify_chain(problem,certificate); t2=perf_counter()
            expected = factorial(n) if family=='S' else factorial(n)//2 if family=='A' else 2*n if family=='D' else n
            assert checked.order==expected
            counts['large_chain_instances'] += 1
            bundle={'name':f'large-{family}-{n}','problem':problem,'chain':certificate,'membership':[],
                    'canonical':[], 'canonical_family':[]}
            if family in ('S','A'):
                sym={'format':'forge.symmetry.family.v1','family':family}
                vf=verify_family(checked,sym); bundle['family']=sym
                colors=[i%3 for i in range(n)]
                image=canonical_family_certificate(search,colors,family)
                assert verify_canonical_family(checked,colors,image)['best']==sorted(colors)
                bundle['canonical_family'].append({'colors':colors,'certificate':image,'expected':sorted(colors)})
                counts['large_family_canonical_queries'] += 1
                bundle['family_counts']=[[q,vf.count_colors(q)] for q in (0,1,2,7,100)]
            (corpus/f'large-{family}-{n}.json').write_text(json.dumps(bundle,separators=(',',':'))+'\n')
            certificates.append(f'large-{family}-{n}')
            large_metrics.append({'case':f'{family}{n}','degree':n,'order':checked.order,
                'strong_generators':len(search.strong),'word_dag_nodes':len(certificate['word_dag']),
                'transversal_entries':sum(len(t) for t in checked.tables),'schreier_checks':checked.schreier_checks,
                'certificate_bytes':len(json.dumps(certificate,separators=(',',':')).encode()),
                'search_seconds':t1-t0,'check_seconds':t2-t1})

    # Syntactic symmetry gates: cycle CNF, then deliberately asymmetric inputs.
    gate_results=[]
    for n in range(4,9):
        problem=named_problem('D',n); chain=verify_chain(problem,build_chain(problem).export())
        clauses=[[i+1,(i+1)%n+1] for i in range(n)]
        assert verify_cnf_symmetry(chain,clauses,[1]*n)
        counts['cnf_symmetry_acceptances']+=1
        for label,c,w in [('asymmetric_clause',clauses+[[1]],[1]*n),
                          ('asymmetric_objective',clauses,[2]+[1]*(n-1))]:
            try: verify_cnf_symmetry(chain,c,w)
            except InvalidCertificate: counts['cnf_symmetry_rejections']+=1
            else: raise AssertionError(label)
        gate_results.append({'degree':n,'accepted':'cycle clauses with uniform objective',
                             'rejected':['added unit clause','unequal objective coefficient']})

    # Deliberate certificate corruptions.  These test rejection, not soundness.
    problem=named_problem('S',5); search=build_chain(problem); base=search.export()
    chain=verify_chain(problem,base)
    controls=[]
    def reject(name, thunk):
        try: thunk()
        except (InvalidCertificate,CheckLimit) as exc:
            controls.append({'name':name,'exception':type(exc).__name__,'reason':str(exc)})
            counts['malformed_or_corrupted_rejections']+=1
        else: raise AssertionError('corruption accepted: '+name)
    def mutate(name, change):
        altered=deepcopy(base);change(altered);reject(name,lambda:verify_chain(problem,altered))
    mutate('wrong-order',lambda c:c.update(order=121))
    mutate('Boolean-order',lambda c:c.update(order=True))
    mutate('float-order',lambda c:c.update(order=120.0))
    mutate('unknown-field',lambda c:c.update(untrusted='extra'))
    mutate('wrong-format',lambda c:c.update(format='another-language'))
    mutate('missing-base-level',lambda c:c['levels'].pop())
    mutate('missing-original-generator',lambda c:c['strong'].pop(0))
    mutate('duplicate-strong-generator',lambda c:c['strong'].append(c['strong'][0]))
    mutate('identity-strong-generator',lambda c:c['strong'].append(0))
    mutate('Boolean-root',lambda c:c['levels'][0][0].__setitem__(0,False))
    mutate('wrong-root',lambda c:c['levels'][0][0].__setitem__(0,1))
    mutate('forward-orbit-parent',lambda c:c['levels'][0][1].__setitem__(1,1))
    mutate('zero-generator-label',lambda c:c['levels'][0][1].__setitem__(2,0))
    mutate('duplicate-orbit-image',lambda c:c['levels'][0][1].__setitem__(0,0))
    mutate('omitted-orbit-leaf',lambda c:c['levels'][0].pop())
    mutate('forward-DAG-reference',lambda c:c['word_dag'].append(['inv',len(c['word_dag'])]))
    mutate('negative-DAG-reference',lambda c:c['word_dag'].append(['mul',-1,0]))
    mutate('unknown-DAG-operator',lambda c:c['word_dag'].append(['oracle']))
    mutate('nonexistent-input-generator',lambda c:c['word_dag'].append(['gen',2]))
    changed=deepcopy(problem);changed['generators']=[list(range(5)),list(range(5))]
    reject('problem-substitution',lambda:verify_chain(changed,base))
    changed=deepcopy(problem);changed['generators'][0][1]=changed['generators'][0][0]
    reject('nonbijective-input',lambda:verify_chain(changed,base))
    changed=deepcopy(problem);changed['degree']=True
    reject('Boolean-degree',lambda:verify_chain(changed,base))
    colors=[2,1,0,2,0];canonical,_=canonical_certificate(search,colors)
    altered=deepcopy(canonical);altered['cover']=['cut']
    reject('unsound-root-prune',lambda:verify_canonical(chain,colors,altered))
    altered=deepcopy(canonical);altered['cover'][1].pop()
    reject('omitted-coset-child',lambda:verify_canonical(chain,colors,altered))
    altered=deepcopy(canonical);altered['best'][0]=7
    reject('false-minimum',lambda:verify_canonical(chain,colors,altered))
    altered=deepcopy(canonical);altered['transporter']=list(range(5))
    reject('wrong-transporter',lambda:verify_canonical(chain,colors,altered))
    census=burnside_certificate(problem)
    altered=deepcopy(census);altered['inventory'][0][1]+=1
    reject('wrong-cycle-multiplicity',lambda:verify_burnside(chain,altered))
    altered=deepcopy(census);altered['inventory'].pop()
    reject('omitted-cycle-class',lambda:verify_burnside(chain,altered))
    alternate=named_problem('A',5);achain=verify_chain(alternate,build_chain(alternate).export())
    reject('unproved-symmetric-family',lambda:verify_family(achain,{'format':'forge.symmetry.family.v1','family':'S'}))
    reject('unproved-alternating-family',lambda:verify_family(chain,{'format':'forge.symmetry.family.v1','family':'A'}))
    for name,text in [('duplicate-JSON-key','{"x":1,"x":2}'),('floating-JSON','{"x":0.0}'),
                      ('nonfinite-JSON','{"x":NaN}')]:
        path=destination/f'{name}.json';path.write_text(text)
        reject(name,lambda p=path:load_json(p));path.unlink()

    # Valid data refused by budgets must be reported as UNKNOWN, not disproved.
    refusals=[]
    def unknown(name,thunk):
        try:thunk()
        except (SearchLimit,CheckLimit) as exc:
            refusals.append({'name':name,'outcome':'unknown','reason':str(exc)})
            counts['resource_refusals']=len(refusals)
        else:raise AssertionError('expected budget refusal: '+name)
    unknown('producer-zero-Schreier-budget',lambda:build_chain(problem,max_steps=0))
    unknown('checker-zero-Schreier-budget',lambda:verify_chain(problem,base,max_checks=0))
    unknown('explicit-census-budget',lambda:burnside_certificate(problem,max_order=10))
    unknown('canonical-proof-node-budget',lambda:verify_canonical(chain,colors,canonical,max_nodes=1))
    s15=build_chain(named_problem('S',15))
    unknown('S15-generic-canonical-20000',lambda:canonical_certificate(s15,[i%3 for i in range(15)],max_nodes=20_000))

    summary={'seed':20260915,'python':sys.version,'platform':platform.platform(),
             'status':'ALL_ASSERTIONS_PASSED','lean_status':'NOT_RUN_NO_EXECUTABLE',
             'unit_note':'Categories are different, sometimes overlapping units; no pooled success rate.',
             'counts':dict(sorted(counts.items())),'corpus_bundles':len(certificates),
             'elapsed_seconds':perf_counter()-started,'large_fixtures':large_metrics,
             'no_claims':['No Lean-kernel certificate replay','No comparison with grind or other Lean tactics',
                          'No polynomial bound for generic canonical-image search or arbitrary cycle inventory']}
    for filename,value in [('summary.json',summary),('small_metrics.json',metrics),
                           ('rejection_controls.json',controls),('resource_refusals.json',refusals),
                           ('cnf_gate_results.json',gate_results),('corpus_manifest.json',certificates)]:
        (destination/filename).write_text(json.dumps(value,indent=2)+'\n')
    return summary

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path('reproduced-results'))
    parser.add_argument('--skip-large',action='store_true')
    args=parser.parse_args()
    print(json.dumps(run(args.output,not args.skip_large),indent=2))
