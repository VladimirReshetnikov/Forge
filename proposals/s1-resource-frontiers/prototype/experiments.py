#!/usr/bin/env python3
"""Reproducible stdlib-only experiments; default output never overwrites evidence.

The forward oracle implements firing directly on the input dictionaries; it
imports neither transition/predecessor arithmetic nor summary code for its work.
A fixed-total-token invariant makes EVERY conservative oracle query finite.
"""
from __future__ import annotations
import argparse
from collections import deque
import copy
import csv
from itertools import product
import json
from pathlib import Path
import platform
import random
import statistics
import sys
from time import perf_counter_ns
import traceback

from forge_resources import producer as P
from forge_resources import checker as C
from forge_resources.model import Net, ResourceSummary, RunDAG
from forge_resources.examples import NAMED, problem, MUTEX, BROKEN_MUTEX, UNBOUNDED_SAFE, STUTTER, DEPLETION

SEED = 20260915


def dump(path, x):
    path.write_text(json.dumps(x, indent=2, sort_keys=True) + '\n')


def below(a, b):
    if len(a) != len(b): raise AssertionError('oracle dimension mismatch')
    return all(x <= y for x, y in zip(a, b))


def fire_raw(p, state, number):
    t = p['transitions'][number]
    if any(state[i] < t['consume'][i] for i in range(p['dimension'])):
        return None
    return tuple(state[i] - t['consume'][i] + t['produce'][i] for i in range(p['dimension']))


def walk_raw(p, start, word):
    state = start
    for t in word:
        state = fire_raw(p, state, t)
        if state is None: return None
    return state


def conservative_oracle(p, start):
    if any(sum(t['consume']) != sum(t['produce']) for t in p['transitions']):
        raise AssertionError('finite oracle used on a nonconservative net')
    queue = deque([start]); visited = {start}; unsafe = False
    while queue:
        state = queue.popleft()
        if any(below(b, state) for b in p['targets']): unsafe = True
        for t in range(len(p['transitions'])):
            dest = fire_raw(p, state, t)
            if dest is not None and dest not in visited:
                if sum(dest) != sum(start): raise AssertionError('broken oracle invariant')
                visited.add(dest); queue.append(dest)
    return unsafe, len(visited)  # Always exhausted, even after finding a target.


def counts_vector(rng, d, total):
    v = [0] * d
    for _ in range(total): v[rng.randrange(d)] += 1
    return v


def record(name, expected, certificate):
    return {'name': name, 'expected': expected, 'certificate': certificate}


def main(out: Path):
    out.mkdir(parents=True, exist_ok=True)
    if (out / 'summary.json').exists():
        raise RuntimeError('output already contains evidence; choose a fresh --out directory')
    rng = random.Random(SEED)
    started = perf_counter_ns()
    summary = {'run_id': 'resource-frontiers-20260915-v1', 'seed': SEED,
               'python': sys.version, 'platform': platform.platform(),
               'lean_status': 'NOT_RUN: no Lean executable available',
               'comparison_with_lean_tactics': 'NOT_RUN',
               'authority': 'Python checks, not Lean-kernel proofs'}
    corpora = {'frontiers': [], 'thresholds': [], 'parameters': [], 'runs': [], 'lassos': []}
    stats = []; fc_by_name = {}

    def add_frontier(name, p):
        result = P.frontier(p)
        if result['status'] != 'CERTIFICATE':
            raise AssertionError(f'frontier budget exhausted in expected-complete suite: {name}')
        cert = result['certificate']; before = perf_counter_ns()
        C.check_frontier(p, cert); check_ns = perf_counter_ns() - before
        fc_by_name[name] = (p, cert)
        corpora['frontiers'].append(record(name, p, cert))
        stats.append({'name': name, **result['stats'], 'check_ns': check_ns})
        return cert

    for name, p in NAMED.items(): add_frontier(name, p)
    for j in range(60):
        d = 2 if j < 20 else 3
        ts = []
        for n in range(rng.randrange(1, 6)):
            total = rng.randrange(1, 4)
            ts.append((f't{n}', counts_vector(rng, d, total), counts_vector(rng, d, total)))
        targets = [[rng.randrange(4) for _ in range(d)] for _ in range(rng.randrange(1, 4))]
        add_frontier(f'conservative_{j:02}', problem(d, ts, targets))

    # Differential forward reachability: all markings of total at most six.
    rows = []; yes = no = visits = 0
    for name, (p, cert) in fc_by_name.items():
        if not name.startswith('conservative_'): continue
        for initial in product(range(7), repeat=p['dimension']):
            if sum(initial) > 6: continue
            truth, states = conservative_oracle(p, initial)
            predicted = any(below(e['marking'], initial) for e in cert['basis'])
            if truth != predicted: raise AssertionError(('forward disagreement', name, initial))
            yes += truth; no += not truth; visits += states
            rows.append({'net': name, 'initial': json.dumps(initial), 'unsafe': truth,
                         'oracle_states_exhausted': states, 'agrees': True})
    with (out / 'forward-oracle.csv').open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
    summary['forward_oracle'] = {'nets': 60, 'queries': len(rows), 'unsafe': yes, 'safe': no,
                                 'state_visits_sum': visits, 'disagreements': 0,
                                 'oracle_cutoffs': 0, 'max_initial_total': 6}

    # Pointwise exhaustive predecessor identity, independent direct transition.
    pred_checks = 0
    for c, p, b in product(range(6), repeat=3):
        minimal = c + max(b - p, 0)
        for m in range(13):
            direct = m >= c and m - c + p >= b
            if direct != (m >= minimal): raise AssertionError(('predecessor', c, p, b, m))
            pred_checks += 1
    summary['predecessor_identity'] = {'coordinate_checks': pred_checks, 'disagreements': 0}

    # Compare natural summaries, independent signed summaries, and concrete runs.
    word_checks = repeated_checks = summary_pairs = 0
    for j in range(1000):
        d = rng.randrange(1, 5)
        p = problem(d, [(f't{i}', [rng.randrange(4) for _ in range(d)],
                        [rng.randrange(4) for _ in range(d)]) for i in range(4)], [])
        net = Net.from_dict(p); word = tuple(rng.randrange(4) for _ in range(rng.randrange(13)))
        natural = ResourceSummary.empty(d)
        for t in word: natural = natural.then(ResourceSummary.step(net.transitions[t]))
        dag = RunDAG(net); root = dag.word(word); nodes, roots = dag.compact([root])
        need, delta, length = C.check_runs(p, nodes)[roots[0]]
        if (need, tuple(need[i] + delta[i] for i in range(d)), length) != (
                natural.need, natural.give, natural.length):
            raise AssertionError('different summary algebras disagree')
        summary_pairs += 1
        samples = [natural.need, tuple(x + rng.randrange(4) for x in natural.need)]
        samples += [tuple(rng.randrange(12) for _ in range(d)) for _ in range(5)]
        for state in samples:
            direct = walk_raw(p, state, word)
            if direct != natural.execute(state): raise AssertionError('word mismatch')
            word_checks += 1
        count = rng.randrange(9); repeated = natural.repeat(count)
        for state in [repeated.need, tuple(rng.randrange(30) for _ in range(d))]:
            if walk_raw(p, state, word * count) != repeated.execute(state):
                raise AssertionError('small expanded power mismatch')
            repeated_checks += 1
    summary['word_algebra'] = {'random_words': 1000, 'dual_summary_agreements': summary_pairs,
                              'concrete_word_queries': word_checks,
                              'expanded_small_power_queries': repeated_checks, 'disagreements': 0}

    # Exact scalar and multiparameter results, plus points beyond certified caps.
    threshold_queries = parameter_queries = total_cells = 0
    for j, (name, (p, fc)) in enumerate(fc_by_name.items()):
        d = p['dimension']
        for trial in range(2):
            a = [rng.randrange(4) for _ in range(d)]; c = [rng.randrange(4) for _ in range(d)]
            cert = P.threshold(p, fc, a, c); C.check_threshold(cert['query'], cert)
            corpora['thresholds'].append(record(f'{name}_{trial}', cert['query'], cert))
            for n in list(range(15)) + [1000, 10**20]:
                actual = any(below(e['marking'], [a[i]*n+c[i] for i in range(d)]) for e in fc['basis'])
                claim = cert['threshold'] is not None and n >= cert['threshold']
                if actual != claim: raise AssertionError('threshold disagreement')
                threshold_queries += 1
        k = 1 + j % 3
        a = [[rng.randrange(4) for _ in range(k)] for _ in range(d)]
        c = [rng.randrange(3) for _ in range(d)]
        result = P.parameters(p, fc, a, c)
        if result['status'] != 'CERTIFICATE': raise AssertionError('unexpected parameter budget')
        cert = result['certificate']; C.check_parameters(cert['query'], cert)
        total_cells += result['box_cells']
        corpora['parameters'].append(record(name, cert['query'], cert))
        for _ in range(100):
            theta = tuple(rng.randrange(0, 3*cap+10) for cap in cert['caps'])
            m = tuple(c[i] + sum(a[i][h]*theta[h] for h in range(k)) for i in range(d))
            actual = any(below(e['marking'], m) for e in fc['basis'])
            predicted = any(below(f, theta) for f in cert['minima'])
            if actual != predicted: raise AssertionError('parameter disagreement')
            parameter_queries += 1
    summary['parameters'] = {'scalar_certificates': len(corpora['thresholds']),
                             'scalar_spot_queries': threshold_queries,
                             'pareto_certificates': len(corpora['parameters']),
                             'certified_grid_cells': total_cells,
                             'large_parameter_spot_queries': parameter_queries,
                             'disagreements': 0}

    # Named exact population conclusions retained separately for the article.
    named_params = {}
    for name in ('mutex', 'broken_mutex'):
        p, fc = fc_by_name[name]
        tc = P.threshold(p, fc, [1, 0, 0], [0, 1, 0])
        C.check_threshold(tc['query'], tc)
        pc = P.parameters(p, fc, [[1, 0], [0, 1], [0, 0]], [0, 0, 0])['certificate']
        C.check_parameters(pc['query'], pc)
        corpora['thresholds'].append(record(name+'_population', tc['query'], tc))
        corpora['parameters'].append(record(name+'_population_permits', pc['query'], pc))
        named_params[name] = {'basis': [x['marking'] for x in fc['basis']],
                              'one_permit_first_unsafe_population': tc['threshold'],
                              'population_permit_minima': pc['minima']}
    dump(out / 'named-conclusions.json', named_params)

    # Compressed witnesses represent the length; they do NOT execute it.
    n = 10**100; net = Net.from_dict(DEPLETION); dag = RunDAG(net)
    root = dag.repeat(dag.step(0), n); nodes, roots = dag.compact([root])
    q = {'problem': DEPLETION, 'initial': [n+1, 0], 'final': [1, n], 'length': n}
    cert = {'schema': 'forge.resources.run.v1', 'query': q, 'runs': nodes, 'root': roots[0]}
    before = perf_counter_ns(); C.check_run(q, cert); check_ns = perf_counter_ns()-before
    corpora['runs'].append(record('10_to_100_firings_represented_not_executed', q, cert))
    summary['compressed_run'] = {'represented_steps': str(n), 'dag_nodes': len(nodes),
                                 'check_ns': check_ns, 'steps_executed': 0,
                                 'meaning': 'exact symbolically summarized run, not an expanded run'}
    for name, p, initial, claim, place in [
            ('grow_output', UNBOUNDED_SAFE, [1, 0], 'unbounded', 1),
            ('stutter_forever', STUTTER, [1], 'nontermination', 0)]:
        result = P.find_lasso(p, initial, claim=claim, place=place)
        if result['status'] != 'CERTIFICATE': raise AssertionError('missing expected lasso')
        cert = result['certificate']; C.check_lasso(cert['query'], cert)
        corpora['lassos'].append(record(name, cert['query'], cert))
    negatives = [P.find_lasso(STUTTER, [1], claim='unbounded'),
                 P.find_lasso(DEPLETION, [10, 0], claim='unbounded', place=1),
                 P.frontier(MUTEX, max_candidates=0),
                 P.parameters(MUTEX, fc_by_name['mutex'][1], [[1,0],[0,1],[0,0]], [0,0,0], max_box=0)]
    if any(r['status'] != 'UNKNOWN' for r in negatives): raise AssertionError('negative authority escalation')
    summary['lassos_and_refusals'] = {'positive_certificates': 2, 'explicit_unknown_controls': len(negatives)}
    dump(out/'unknown-controls.json', negatives)

    # Deliberately invalid mutations; each change has a semantic/structural reason.
    mutations = []
    base = corpora['frontiers'][0]
    for basis_index in range(len(base['certificate']['basis'])):
        if base['certificate']['basis'][basis_index]['run'] == 0: continue
        bad = copy.deepcopy(base)
        bad['certificate']['basis'][basis_index]['run'] = 0
        mutations.append((f'deleted_positive_witness_{basis_index}', bad))
    bad = copy.deepcopy(base); bad['certificate']['predecessor_cover'][0] = []
    mutations.append(('missing_transition_obligations', bad))
    bad = copy.deepcopy(base); bad['certificate']['target_cover'] = []
    mutations.append(('missing_bad_target_obligation', bad))
    bad = copy.deepcopy(base); bad['certificate']['problem']['transitions'][0]['consume'][1] = 0
    mutations.append(('changed_net_binding', bad))
    bad = copy.deepcopy(corpora['runs'][0]); bad['certificate']['query']['initial'][0] -= 1
    bad['expected'] = copy.deepcopy(bad['certificate']['query'])
    mutations.append(('nonnegative_endpoint_but_disabled_run', bad))
    bad = copy.deepcopy(corpora['lassos'][0]); bad['certificate']['loop'] = 0
    mutations.append(('empty_infinite_loop', bad))
    bad = copy.deepcopy(corpora['parameters'][-2]); bad['certificate']['minima'] = [[0,0]]
    mutations.append(('false_parameter_minimum', bad))
    outcomes = []
    for name, bad in mutations:
        try: C.check_record(bad)
        except C.InvalidCertificate as exc:
            outcomes.append({'name': name, 'result': 'REJECTED', 'diagnostic': str(exc)})
        else: raise AssertionError(('accepted corruption', name))
    dump(out / 'mutation-results.json', outcomes)
    with (out/'invalid-mutations.jsonl').open('w') as f:
        for name,bad in mutations: f.write(json.dumps({'mutation':name,'invalid_record':bad})+'\n')
    summary['mutations'] = {'deliberately_invalid_records': len(mutations), 'rejected': len(outcomes)}

    for kind, records in corpora.items():
        with (out / f'{kind}.jsonl').open('w') as f:
            for item in records: f.write(json.dumps(item, sort_keys=True) + '\n')
    with (out / 'frontier-costs.csv').open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(stats[0])); w.writeheader(); w.writerows(stats)
    summary['corpora'] = {k: len(v) for k, v in corpora.items()}
    summary['frontier_costs'] = {'median_search_ms': statistics.median(s['search_ns'] for s in stats)/1e6,
                                'median_check_ms': statistics.median(s['check_ns'] for s in stats)/1e6,
                                'maximum_basis': max(s['final_basis'] for s in stats),
                                'total_dominance_deletions': sum(s['deletions'] for s in stats),
                                'maximum_candidates': max(s['candidates'] for s in stats)}
    summary['elapsed_seconds'] = (perf_counter_ns()-started)/1e9
    dump(out / 'summary.json', summary)
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=Path('reproduced-results'))
    args = parser.parse_args()
    try: main(args.out)
    except Exception:
        args.out.mkdir(parents=True, exist_ok=True)
        (args.out/'FAILED_RUN.txt').write_text(traceback.format_exc())
        raise
