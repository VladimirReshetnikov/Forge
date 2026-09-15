"""Demand-directed Horn search. Ported from p5, p8, p9 and p3."""
from dataclasses import replace
import random
import pytest
from forge.horn import (Term, Atom, Rule, ProofNode, HornCertificate, check_horn,
                        demand_prove, forward_prove, trim, minimize, chain_problem)


def horn_family(depth):
    """p5's branching family: 2^(d+1)-1 facts forward, d+1 demands backward."""
    x, a = Term('?x'), Term('a')
    P = lambda t: Atom('P', (t,))
    rules = (Rule('grow_g', P(Term('g', (x,))), (P(x),)),
             Rule('grow_f', P(Term('f', (x,))), (P(x),)))
    t = a
    for _ in range(depth):
        t = Term('f', (t,))
    return (P(a),), rules, P(t)


@pytest.mark.parametrize('depth', [1, 2, 4, 6, 8, 10])
def test_demand_forward_agree(depth):
    facts, rules, goal = horn_family(depth)
    d = demand_prove(facts, rules, goal)
    f = forward_prove(facts, rules, goal)
    assert d.status == f.status == 'proved'
    assert d.terms_or_facts == depth + 1
    assert f.terms_or_facts == 2 ** (depth + 1) - 1
    assert check_horn(facts, rules, goal, d.certificate)
    assert check_horn(facts, rules, goal, f.certificate)


def test_horn_cycles_and_and_branches():
    """p5: a tabled fixed point -- a cycle alone never proves a fact."""
    a = Term('a')
    A = lambda p: Atom(p, (a,))
    rules = (Rule('cycle1', A('P'), (A('Q'),)), Rule('cycle2', A('Q'), (A('P'),)),
             Rule('join', A('R'), (A('P'), A('Q'))))
    assert demand_prove((), rules, A('R')).status == 'unknown'
    assert forward_prove((), rules, A('R')).status == 'unknown'
    assert demand_prove((A('P'),), rules, A('R')).status == 'proved'
    assert forward_prove((A('P'),), rules, A('R')).status == 'proved'


@pytest.mark.parametrize('bad', ['circular', 'wrong_rule', 'no_facts', 'wrong_goal',
                                 'bad_root', 'variable_goal', 'nonground_substitution'])
def test_horn_certificate_tampering(bad):
    """p9's parametrized bad-input matrix over p5's proof DAG."""
    facts, rules, goal = horn_family(3)
    c = demand_prove(facts, rules, goal).certificate
    assert check_horn(facts, rules, goal, c)
    if bad == 'circular':
        nodes = list(c.nodes)
        nodes[-1] = replace(nodes[-1], premises=(len(nodes) - 1,))
        c = replace(c, nodes=tuple(nodes))
    elif bad == 'wrong_rule':
        nodes = list(c.nodes)
        nodes[-1] = replace(nodes[-1], rule=0)
        c = replace(c, nodes=tuple(nodes))
    elif bad == 'no_facts':
        facts = ()
    elif bad == 'wrong_goal':
        goal = facts[0]
    elif bad == 'bad_root':
        c = replace(c, root=-1)
    elif bad == 'variable_goal':
        goal = Atom('P', (Term('?x'),))
    else:
        nodes = list(c.nodes)
        nodes[-1] = replace(nodes[-1], substitution=(('?x', Term('?y')),))
        c = replace(c, nodes=tuple(nodes))
    assert not check_horn(facts, rules, goal, c)


def test_minimize_keeps_the_proof_valid():
    """p8: minimisation must never break replay."""
    facts, rules, goal = chain_problem(6, 4)
    r = demand_prove(facts, rules, goal)
    assert r.status == 'proved'
    small = minimize(r.certificate)
    assert check_horn(facts, rules, goal, small)
    assert len(small.nodes) <= len(r.certificate.nodes)
    assert len(small.nodes) == 7  # one fact plus six chain steps


def test_stop_at_goal_knob():
    """p8: stopping at the goal changes work done, never the answer."""
    facts, rules, goal = chain_problem(5, 20)
    early = demand_prove(facts, rules, goal, stop_at_goal=True)
    full = demand_prove(facts, rules, goal, stop_at_goal=False)
    assert early.status == full.status == 'proved'
    assert check_horn(facts, rules, goal, early.certificate)
    assert check_horn(facts, rules, goal, full.certificate)


def test_index_and_search_timings_are_separated():
    """p3: index construction is accounted for, not hidden from the comparison."""
    facts, rules, goal = chain_problem(20, 200)
    r = demand_prove(facts, rules, goal)
    assert r.status == 'proved'
    assert r.index_seconds >= 0 and r.search_seconds >= 0
    with pytest.raises(ValueError):
        chain_problem(0, 1)


def test_missing_guard_is_not_assumed():
    """p9: an unproved side condition blocks the proof."""
    x, a = Term('?x'), Term('a')
    rules = (Rule('guarded', Atom('Q', (x,)), (Atom('P', (x,)), Atom('G', (x,)))),)
    facts, goal = (Atom('P', (a,)),), Atom('Q', (a,))
    assert demand_prove(facts, rules, goal).status == 'unknown'
    facts = facts + (Atom('G', (a,)),)
    r = demand_prove(facts, rules, goal)
    assert r.status == 'proved' and check_horn(facts, rules, goal, r.certificate)


def test_abstains_on_unbound_premise():
    """p9: the engine never invents a value for a free body variable."""
    x, y, a = Term('?x'), Term('?y'), Term('a')
    rules = (Rule('unbound', Atom('Q', (x,)), (Atom('P', (y,)),)),)
    assert not rules[0].head_covered
    facts, goal = (Atom('P', (a,)),), Atom('Q', (a,))
    assert demand_prove(facts, rules, goal).status == 'unknown'
    assert forward_prove(facts, rules, goal).status == 'unknown'


def test_budgets_return_unknown():
    facts, rules, goal = horn_family(8)
    assert demand_prove(facts, rules, goal, max_depth=4).status == 'unknown'
    assert demand_prove(facts, rules, goal, max_demands=3).status == 'unknown'
    assert forward_prove(facts, rules, goal, max_facts=3, max_depth=8).status == 'unknown'
    with pytest.raises(ValueError):
        demand_prove((), (), Atom('P', (Term('?x'),)))


@pytest.mark.parametrize('seed', range(15))
def test_ground_horn_differential(seed):
    """p5: the two engines must agree on every random ground program."""
    rng = random.Random(seed)
    a = Term('a')
    atoms = [Atom(f'P{i}', (a,)) for i in range(12)]
    facts = tuple(rng.sample(atoms, 3))
    rules = tuple(Rule(f'r{j}', rng.choice(atoms),
                       tuple(rng.sample(atoms, rng.randint(1, 3)))) for j in range(22))
    for goal in atoms:
        d = demand_prove(facts, rules, goal)
        f = forward_prove(facts, rules, goal)
        assert d.status == f.status
        if d.certificate:
            assert check_horn(facts, rules, goal, d.certificate)
        if f.certificate:
            assert check_horn(facts, rules, goal, f.certificate)


def test_terms_reject_non_leaf_variables():
    with pytest.raises(ValueError):
        Term('?x', (Term('a'),))
    assert Term('f', (Term('?x'),)).variables() == {'?x'}
    assert Term('a').depth == 0 and Term('f', (Term('a'),)).depth == 1
    assert Atom('P', (Term('f', (Term('a'),)),)).text() == 'P(f(a))'
