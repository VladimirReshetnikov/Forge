#!/usr/bin/env python3
"""Export the article's worked examples; no third-party packages.

Run from prototype/: python -S examples.py --output ../reproduced-results/examples
The corpus can be passed to replay.py, whose process forbids solver imports.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path
from forge_ap.models import Arena, Transport, MDP, Simulation, encq
from forge_ap import search, check


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', default='reproduced-results/examples')
    args = parser.parse_args()
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)
    if (out / 'summary.json').exists():
        raise SystemExit('Choose a fresh output directory.')
    records: list[dict] = []
    summaries: list[dict] = []

    def add(name, p, c, summary):
        record = {'id': name, 'problem': p.obj(), 'certificate': c}
        check.check_record(record)
        records.append(record)
        summaries.append({'id': name, **summary})

    for name, p, player in [
        ('parity-infinite-good-cycle', Arena((0, 1), (1, 2), ((1,), (0,))), 0),
        ('parity-good-priority-only-once', Arena((0, 0), (2, 1), ((1,), (1,))), 1),
    ]:
        c = search.solve_parity(p)
        assert c['regions'][player]['vertices'] == [0, 1]
        add(name, p, c, {'winner_of_both_vertices': player})

    problems = [
        ('coupled-fair-bits', Transport((Q(1,2), Q(1,2)), (Q(1,2), Q(1,2)),
            ((True, False), (False, True))), Q(0)),
        ('monotone-bernoulli', Transport((Q(2,3), Q(1,3)), (Q(1,3), Q(2,3)),
            ((True, True), (False, True))), Q(0)),
        ('impossible-perfect-monotone-coupling', Transport((Q(1,3), Q(2,3)),
            (Q(2,3), Q(1,3)), ((True, True), (False, True))), Q(1,3)),
        ('two-coins-versus-binomial', Transport((Q(1,4),)*4,
            (Q(1,4), Q(1,2), Q(1,4)),
            tuple(tuple(a+b == y for y in range(3)) for a,b in [(0,0),(0,1),(1,0),(1,1)])), Q(0)),
    ]
    for name, p, expected in problems:
        c = search.solve_transport(p)
        assert Q(*c['bad_mass']) == expected
        independent = sum((p.mu[i]*p.nu[j] for i in range(len(p.mu))
            for j in range(len(p.nu)) if not p.relation[i][j]), Q(0))
        if name == 'two-coins-versus-binomial':
            assert independent == Q(5,8)
        add(name, p, c, {'optimal_defect': encq(expected),
                         'independent_product_defect': encq(independent)})

    p = MDP((((Q(1,2), Q(1,2)), (Q(3,4), Q(1,4))),
             ((Q(0), Q(1)),)), (1,), 0)
    c = search.solve_mdp(p)
    assert c['outcome'] == 'optimal_bound' and c['values'][0] == [4,1]
    assert c['policy'][0] == 1
    add('adversarial-geometric-retry', p, c,
        {'exact_worst_expectation': [4,1], 'tight_action': 1})

    p = MDP((((Q(0),Q(1)), (Q(1),Q(0))), ((Q(0),Q(1)),)), (1,), 0)
    c = search.solve_mdp(p)
    assert c['outcome'] == 'nontermination' and c['probability_lower'] == [1,1]
    add('good-policy-is-not-universal-termination', p, c,
        {'nontermination_probability_lower': [1,1]})

    actions = (((Q(1),Q(0)), (Q(0),Q(1))),)*2
    p = Simulation(actions, actions, ((True,False), (False,True)))
    c = search.solve_simulation(p)
    matches = [r['right_action'] for r in c['matches']]
    assert c['survivors'] == [[0,0],[1,1]] and matches == [0,1,0,1]
    add('forall-source-action-exists-target-action', p, c,
        {'survivors': c['survivors'], 'target_action_table': matches})

    (out / 'corpus.json').write_text(json.dumps(records, indent=2) + '\n')
    report = {'status': 'PASS', 'examples': summaries, 'lean': 'NOT_RUN'}
    (out / 'summary.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
