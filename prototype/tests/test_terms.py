"""Typed first-order terms. Ported from p9's and p3's term-layer tests."""
import pytest
from forge.terms import (T, V, F, NIL, ZERO, SIG, SORTS, Rule, Step, at, replace,
                         match, subst, vars_of, well_typed, make_rule, normalize,
                         replay, parse_term, DEFINITIONS)


def test_sorts_are_enforced_at_construction():
    with pytest.raises(ValueError):
        F('app', V('h', 'Elem'), NIL)
    with pytest.raises(ValueError):
        F('cons', V('xs'), NIL)
    with pytest.raises(KeyError):
        F('nope', NIL)
    assert match(V('x', 'Elem'), NIL) is None


def test_nat_sort_is_available():
    """p3's Nat fragment folded into p9's signature."""
    assert 'Nat' in SORTS
    assert SIG['add'] == (('Nat', 'Nat'), 'Nat')
    assert SIG['length'] == (('List',), 'Nat')
    t = F('add', ZERO, F('length', NIL))
    assert well_typed(t) and t.sort == 'Nat'
    out, trace = normalize(t, DEFINITIONS)
    assert out == ZERO and trace


def test_length_of_append_normalises():
    xs = F('cons', V('h', 'Elem'), NIL)
    out, _ = normalize(F('length', F('app', xs, xs)), DEFINITIONS)
    assert out == F('s', F('s', ZERO))


def test_well_typed_rejects_junk():
    assert not well_typed(T('nope', (), 'List'))
    assert not well_typed(T('nil', (), 'Elem'))
    assert not well_typed(T('?x', (NIL,), 'List'))
    assert well_typed(T('$c', (), 'Nat'))
    assert not well_typed(T('$c', (), 'Bogus'))


def test_paths_and_replacement():
    t = F('app', NIL, F('rev', NIL))
    assert at(t, (1, 0)) == NIL
    assert replace(t, (1,), NIL) == F('app', NIL, NIL)
    with pytest.raises(ValueError):
        at(t, (5,))
    with pytest.raises(ValueError):
        replace(t, (), V('h', 'Elem'))


def test_flexible_variable_sets_restrict_matching():
    """p4: a rule can declare which of its variables may be instantiated."""
    xs, ys = V('xs'), V('ys')
    open_rule = make_rule('open', F('app', xs, ys), ys)
    closed = make_rule('closed', F('app', xs, ys), ys, flexible=('?ys',))
    target = F('app', NIL, NIL)
    assert match(open_rule.lhs, target, None, open_rule.instantiable()) is not None
    assert match(closed.lhs, target, None, closed.instantiable()) is None
    assert open_rule.instantiable() == {'?xs', '?ys'}
    assert closed.instantiable() == {'?ys'}
    with pytest.raises(ValueError):
        make_rule('bad', F('app', xs, NIL), ys)
    with pytest.raises(ValueError):
        make_rule('bad', F('app', xs, NIL), xs, flexible=('?absent',))


def test_replay_checks_but_never_searches():
    xs = V('xs')
    start = F('app', NIL, xs)
    table = {r.name: r for r in DEFINITIONS}
    assert replay(start, (Step((), 'app.nil'),), table) == xs
    assert replay(start, (Step((), 'rev.nil'),), table) is None
    assert replay(start, (Step((7,), 'app.nil'),), table) is None
    assert replay(start, (Step((), 'no.such.rule'),), table) is None


def test_normalize_respects_its_budget():
    xs = V('xs')
    with pytest.raises(RuntimeError):
        normalize(F('app', NIL, F('app', NIL, xs)), DEFINITIONS, budget=1)


def test_json_round_trip_and_gate():
    t = F('revAcc', F('cons', V('h', 'Elem'), NIL), NIL)
    assert parse_term(t.json()) == t
    bad = t.json()
    bad['sort'] = 'Elem'
    with pytest.raises(ValueError):
        parse_term(bad)
    with pytest.raises(ValueError):
        parse_term({'symbol': 'nil', 'sort': 'List'})


def test_substitution_is_sort_checked():
    xs = V('xs')
    assert subst(F('rev', xs), {'?xs': NIL}) == F('rev', NIL)
    with pytest.raises(ValueError):
        subst(F('rev', xs), {'?xs': V('h', 'Elem')})
    with pytest.raises(ValueError):
        vars_of(F('app', T('?x', (), 'List'), F('cons', T('?x', (), 'Elem'), NIL)))


def test_definitions_are_well_formed():
    assert len({r.name for r in DEFINITIONS}) == len(DEFINITIONS)
    assert all(r.valid_shape() for r in DEFINITIONS)
