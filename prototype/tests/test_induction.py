"""Structural induction. Ported from p4's, p2's and p9's induction suites."""
import copy
import random
import pytest
from forge.terms import V, F, NIL, Step, DEFINITIONS, make_rule, rigid
from forge import induction as I


def test_seed_lemmas_are_proved_and_replayable():
    """p4: every schema is either proved, refuted by a sample, or unknown."""
    verified, records = I.synthesize_lemmas()
    status = {r['name']: r['status'] for r in records}
    assert status['app_right_id'] == 'proved'
    assert status['app_assoc'] == 'proved'
    assert status['rev_app'] == 'proved'
    # revAcc is NOT associative and has no right identity; sampling rejects both.
    assert status['revAcc_right_id'] == 'rejected_by_counterexample'
    assert status['revAcc_assoc'] == 'rejected_by_counterexample'
    assert I.verify_bundle(records, ('app_right_id', 'app_assoc', 'rev_app'))


def test_bundle_rejects_missing_and_reordered_dependencies():
    """p4: anti-circularity -- a lemma may only use STRICTLY earlier lemmas."""
    _, records = I.synthesize_lemmas()
    proved = [r for r in records if r['status'] == 'proved']
    assert len(proved) >= 3
    assert not I.verify_bundle(list(reversed(records)),
                               ('app_right_id', 'app_assoc', 'rev_app'))
    assert not I.verify_bundle(records, ('not_a_lemma',))
    dropped = [r for r in records if r['name'] != 'app_right_id']
    assert not I.verify_bundle(dropped, ('rev_app',))


def test_reserved_names_cannot_be_reused():
    _, records = I.synthesize_lemmas()
    bad = copy.deepcopy(records)
    for r in bad:
        if r['status'] == 'proved':
            r['name'] = 'IH'
            break
    assert not I.verify_bundle(bad)
    bad = copy.deepcopy(records)
    for r in bad:
        if r['status'] == 'proved':
            r['name'] = 'app.nil'
            break
    assert not I.verify_bundle(bad)


def test_automatic_accumulator_generalization():
    """p2 + p9: the goal needs generalization; the RHS is enumerated, not given."""
    bank = I.standard_bank()
    xs = V('xs')
    lhs, rhs = F('revAcc', xs, NIL), F('rev', xs)
    assert I.prove(lhs, rhs, bank.rules) is None  # direct induction fails
    found = I.discover_accumulator_lemma(lhs, rhs, bank.rules)
    assert found.changed_arguments == (1,)
    assert found.rhs == F('app', F('rev', xs), V('acc1'))
    assert found.certificate is not None
    assert I.verify(found.lhs, found.rhs, found.certificate, bank.rules)
    assert found.sample_survivors >= 1 and found.enumerated > found.sample_survivors


def test_small_grammar_limit_returns_no_proof():
    """p2: too small a grammar is UNKNOWN, not a refutation."""
    bank = I.standard_bank()
    xs = V('xs')
    found = I.discover_accumulator_lemma(F('revAcc', xs, NIL), F('rev', xs),
                                         bank.rules, max_size=2)
    assert found.certificate is None


def test_full_pipeline_specializes_instead_of_assuming():
    """p9: the original goal is RE-DERIVED from the accepted general lemma."""
    bank, stats = I.synthesize_accumulator()
    assert stats['status'] == 'certified'
    assert stats['direct_induction_succeeded'] is False
    assert stats['specialization_checked'] is True
    assert [r.name for r in bank.rules] == ['app_right_nil', 'app_assoc', 'revAcc_spec']
    replayed = I.TheoremBank()
    for name, (lhs, rhs, cert) in bank.certificates.items():
        assert replayed.add(name, lhs, rhs, cert)


def test_theorem_bank_rejects_duplicates_and_reserved_names():
    bank = I.standard_bank()
    lhs, rhs, cert = bank.certificates['app_right_nil']
    assert not bank.add('app_right_nil', lhs, rhs, cert)
    assert not bank.add('IH', lhs, rhs, cert)
    assert not bank.add('app.nil', lhs, rhs, cert)


@pytest.mark.parametrize('bad', ['truncated_base', 'truncated_step', 'bad_generalized',
                                 'duplicate_generalized', 'wrong_induct', 'false_goal',
                                 'future_rule', 'missing_lemma', 'reserved_collision'])
def test_induction_rejects_mutations(bad):
    """p9's parametrized bad-input matrix, on p4's explicit-substitution traces."""
    bank = I.standard_bank()
    lhs, rhs, cert = bank.certificates['app_assoc']
    cert = copy.deepcopy(cert)
    lemmas = bank.rules[:1]
    if bad == 'truncated_base':
        cert['branches'][0]['left'] = cert['branches'][0]['left'][:-1]
    elif bad == 'truncated_step':
        cert['branches'][1]['left'] = cert['branches'][1]['left'][:-1]
    elif bad == 'bad_generalized':
        cert['generalized'] = ['?absent']
    elif bad == 'duplicate_generalized':
        cert['generalized'] = ['?ys', '?ys']
    elif bad == 'wrong_induct':
        cert['induct'] = '?ys'
    elif bad == 'false_goal':
        rhs = NIL
    elif bad == 'future_rule':
        cert['branches'][1]['left'] = [{'path': [], 'rule': 'future_lemma', 'subst': {}}]
    elif bad == 'missing_lemma':
        cert['branches'][1]['left'] = [{'path': [], 'rule': 'app_right_nil', 'subst': {}}]
        lemmas = ()
    else:
        lhs = F('app', F('app', V('_tail'), V('ys')), V('zs'))
        rhs = F('app', V('_tail'), F('app', V('ys'), V('zs')))
    assert not I.verify(lhs, rhs, cert, lemmas)


def test_ih_tail_is_rigid():
    """p4/p9: the induction hypothesis is NOT a universally applicable theorem."""
    xs, acc = V('xs'), V('acc')
    _, _, ih = I.branches(F('revAcc', xs, acc), F('app', F('rev', xs), acc),
                          '?xs', ('?acc',))
    from forge.terms import match
    flexible = ih.instantiable()
    assert flexible == {'?acc'}
    # The tail may not be instantiated: only the generalised accumulator may vary.
    assert match(ih.lhs, F('revAcc', NIL, NIL), None, flexible) is None
    assert match(ih.lhs, F('revAcc', V('_tail'), NIL), None, flexible) is not None


def test_generalization_is_required_not_cosmetic():
    bank = I.standard_bank()
    xs, acc = V('xs'), V('acc')
    lhs, rhs = F('revAcc', xs, acc), F('app', F('rev', xs), acc)
    assert I.prove(lhs, rhs, bank.rules, '?xs', generalize=False) is None
    cert = I.prove(lhs, rhs, bank.rules, '?xs')
    assert cert is not None and cert['generalized'] == ['?acc']
    assert I.verify(lhs, rhs, cert, bank.rules)
    assert not I.verify(lhs, rhs, {**cert, 'generalized': []}, bank.rules)


def test_false_statements_are_not_proved():
    bank = I.standard_bank()
    xs = V('xs')
    assert I.prove(F('rev', xs), xs, bank.rules) is None
    assert I.sampled_counterexample(F('rev', xs), xs) is not None
    assert I.sampled_counterexample(F('app', xs, NIL), xs) is None


def test_induction_requires_a_list_variable():
    with pytest.raises(ValueError):
        I.branches(F('app', NIL, NIL), NIL, '?xs', ())
    with pytest.raises(ValueError):
        I.branches(F('app', V('xs'), NIL), V('xs'), '?xs', ('?xs',))
    assert I.prove(F('app', V('xs'), NIL), V('xs'), (), '?nope') is None


@pytest.mark.parametrize('seed', range(20))
def test_random_semantic_crosscheck(seed):
    """p2: every accepted equation must also hold on random concrete lists."""
    rng = random.Random(seed)
    bank, _ = I.synthesize_accumulator()
    values = {name: tuple(rng.randrange(5) for _ in range(rng.randrange(6)))
              for name in ('?xs', '?ys', '?zs', '?acc1', '?acc', '?_tail')}
    for lhs, rhs, _ in bank.certificates.values():
        assert I.eval_term(lhs, values) == I.eval_term(rhs, values)


def test_enumerate_list_terms_is_typed_and_ordered():
    """p2: a typed grammar enumerated by node count, with no duplicates."""
    atoms = [NIL, V('xs')]
    terms = list(I.enumerate_list_terms(atoms, 3))
    assert terms[:2] == sorted(atoms, key=str)
    assert len(terms) == len(set(terms))
    assert all(t.sort == 'List' for t in terms)
    with pytest.raises(ValueError):
        list(I.enumerate_list_terms([V('h', 'Elem')], 2))


def test_changed_recursive_arguments():
    assert I.changed_recursive_arguments('revAcc') == {1}
    assert I.changed_recursive_arguments('app') == set()
    with pytest.raises(ValueError):
        I.changed_recursive_arguments('nope')
