"""CDCL(T) over CNF + integer difference logic. Ported from p6 and p4.

The centrepiece is p6's differential test: for every random instance the solver's
answer is compared against an INDEPENDENT oracle (Boolean enumeration plus a
None-sentinel Floyd-Warshall), and every UNSAT answer must carry a proof that
replays -- and whose truncation must NOT replay.
"""
import copy
import itertools
import random
import pytest
from forge.sat import (DiffAtom, Solver, replay, rup_check, check_cycle,
                       floyd_consistent, dpll, normalize_clause, edge,
                       solve_resolution, verify_resolution, verify_sat,
                       exhaustive_oracle, pigeonhole)


def truth(n, clauses, atoms):
    return any(all(any(bits[abs(l) - 1] == (l > 0) for l in c) for c in clauses)
               and floyd_consistent(atoms, bits)
               for bits in itertools.product([False, True], repeat=n))


@pytest.mark.parametrize('mode,count', [('cnf', 120), ('idl', 80)])
def test_differential_against_independent_oracle(mode, count):
    """p6: answer, model and proof are all cross-checked, case by case."""
    rng = random.Random(20260914 if mode == 'cnf' else 20260915)
    sat_count = unsat_count = replayed = truncated = 0
    for _ in range(count):
        n = rng.randrange(3, 8)
        m = rng.randrange(1, 4 * n + 1)
        clauses = [[v * rng.choice([-1, 1]) for v in rng.sample(range(1, n + 1), 3)]
                   for _ in range(m)]
        atoms = {}
        if mode == 'idl':
            for k in range(1, n):
                x, y = rng.sample(range(4), 2)
                atoms[k] = DiffAtom(x, y, rng.randrange(-3, 4))
        expected = truth(n, clauses, atoms)
        s = Solver(n, clauses, atoms)
        got = s.solve()
        assert got == expected
        if got:
            sat_count += 1
            bits = [v == 1 for v in s.a[1:]]
            assert all(any(bits[abs(l) - 1] == (l > 0) for l in c) for c in clauses)
            assert floyd_consistent(atoms, bits)
        else:
            unsat_count += 1
            assert replay(n, clauses, atoms, s.proof)
            replayed += 1
            assert not replay(n, clauses, atoms, s.proof[:-1])
            truncated += 1
    assert sat_count and unsat_count and replayed == unsat_count == truncated


def test_edge_cases():
    """p6: empty CNF, empty clause, tautology, opposing units."""
    for n, clauses, want in [(0, [], True), (0, [[]], False), (1, [[1, -1]], True),
                             (1, [[1], [-1]], False), (2, [[1, 1], [2]], True)]:
        s = Solver(n, clauses)
        assert s.solve() == want
        if not want:
            assert replay(n, clauses, {}, s.proof)
    assert normalize_clause([1, -1], 1) is None
    assert normalize_clause([2, 1, 1], 2) == (1, 2)
    with pytest.raises(ValueError):
        normalize_clause([3], 2)
    with pytest.raises(ValueError):
        Solver(-1, [])


def test_theory_mutations_are_rejected():
    """p6: a flipped cycle literal and a truncated clause must both fail."""
    atoms = {1: DiffAtom(0, 1, 0), 2: DiffAtom(1, 2, 0), 3: DiffAtom(2, 0, -1)}
    s = Solver(3, [[1], [2], [3]], atoms)
    assert s.solve() is False
    assert replay(3, s.original, atoms, s.proof)
    bad = copy.deepcopy(s.proof)
    bad[0]['cycle'][0] *= -1
    assert not replay(3, s.original, atoms, bad)
    bad = copy.deepcopy(s.proof)
    bad[0]['clause'] = bad[0]['clause'][:-1]
    assert not replay(3, s.original, atoms, bad)
    bad = copy.deepcopy(s.proof)
    bad[0]['kind'] = 'nonsense'
    assert not replay(3, s.original, atoms, bad)


def test_check_cycle_duplicates_the_negation_rule():
    """p6: check_cycle never calls edge(); the two must still agree."""
    atoms = {1: DiffAtom(0, 1, 0), 2: DiffAtom(1, 0, -1)}
    cycle = [1, 2]
    clause = tuple(sorted((-l for l in cycle), key=lambda x: (abs(x), x < 0)))
    assert check_cycle(atoms, clause, cycle)
    assert not check_cycle(atoms, clause, [1])
    assert not check_cycle(atoms, clause, [])
    assert not check_cycle({}, clause, cycle)
    assert edge(atoms[1], 1) == (1, 0, 0)
    assert edge(atoms[1], -1) == (0, 1, -1)


def test_large_integer_oracle_and_negation():
    """p6: the None sentinel matters; a finite one would be wrong here."""
    huge = 10 ** 60
    assert floyd_consistent({1: DiffAtom(0, 1, huge)}, [True])
    assert not floyd_consistent({1: DiffAtom(0, 1, huge), 2: DiffAtom(1, 0, -huge - 1)},
                                [True, True])
    # A false difference atom is complemented with -c-1, not -c (INTEGERS ONLY).
    assert not floyd_consistent({1: DiffAtom(0, 0, 0)}, [False])
    assert floyd_consistent({}, [])
    with pytest.raises(ValueError):
        DiffAtom(-1, 0, 0)


def test_rup_check_is_independent():
    """p6: RUP replay does its own unit propagation, not the solver's."""
    db = [(1, 2), (-1, 2)]
    assert rup_check(db, (2,))
    assert not rup_check(db, (1,))
    assert rup_check(db, (1, -1))  # a tautology is trivially RUP


@pytest.mark.parametrize('name,n,clauses', [
    ('padded-core-0', 2, [[1, 2], [1, -2], [-1, 2], [-1, -2]]),
    ('padded-core-4', 6, [[5, 6], [5, -6], [-5, 6], [-5, -6]]),
    ('pigeonhole-4-3', 12, pigeonhole(4, 3)),
])
def test_cdcl_versus_dpll_baseline(name, n, clauses):
    """p6: both engines must reach UNSAT, and the proof must replay."""
    baseline, stats = dpll(n, clauses)
    s = Solver(n, clauses)
    assert baseline is False and s.solve() is False
    assert replay(n, clauses, {}, s.proof)
    assert stats['decisions'] >= 0 and s.stats.conflicts > 0


def test_resolution_proof_mode():
    """p4: the same refutations, as an explicitly resolved proof DAG."""
    holes = pigeonhole(4, 3)
    r = solve_resolution(holes)
    assert r['status'] == 'unsat'
    assert verify_resolution(holes, {}, None, r)
    assert r['stats']['resolutions'] > 0
    bad = copy.deepcopy(r)
    bad['root'] = 0
    assert not verify_resolution(holes, {}, None, bad)
    bad = copy.deepcopy(r)
    for step in bad['proof']:
        if step['kind'] == 'resolution':
            step['pivot'] = -step['pivot']
            break
    assert not verify_resolution(holes, {}, None, bad)


def test_resolution_theory_lemmas():
    atoms = {1: DiffAtom(0, 1, 0), 2: DiffAtom(1, 2, 0), 3: DiffAtom(2, 0, -1)}
    clauses = [[1], [2], [3]]
    r = solve_resolution(clauses, atoms)
    assert r['status'] == 'unsat' and r['stats']['theory_lemmas'] >= 1
    assert verify_resolution(clauses, atoms, None, r)
    bad = copy.deepcopy(r)
    for step in bad['proof']:
        if step['kind'] == 'theory':
            step['cycle'] = step['cycle'][:-1]
            break
    assert not verify_resolution(clauses, atoms, None, bad)
    with pytest.raises(ValueError):
        solve_resolution([[0]])
    with pytest.raises(ValueError):
        solve_resolution([[1]], {1: DiffAtom(9, 9, 0)}, 2)


@pytest.mark.parametrize('seed', range(25))
def test_resolution_mode_matches_the_oracle(seed):
    """p4's verify_sat / exhaustive_oracle, differentially against p6's atoms."""
    rng = random.Random(7000 + seed)
    n = rng.randrange(2, 6)
    clauses = [[v * rng.choice([-1, 1]) for v in rng.sample(range(1, n + 1), 2)]
               for _ in range(rng.randrange(1, 3 * n))]
    atoms = {k: DiffAtom(*rng.sample(range(3), 2), rng.randrange(-2, 3))
             for k in range(1, n)}
    expected = exhaustive_oracle(clauses, atoms)
    r = solve_resolution(clauses, atoms)
    assert (r['status'] == 'sat') == expected
    if expected:
        assert verify_sat(clauses, atoms, None, r)
        assert not verify_resolution(clauses, atoms, None, r)
    else:
        assert verify_resolution(clauses, atoms, None, r)
        assert not verify_sat(clauses, atoms, None, r)


def test_conflict_limit_is_unknown_not_unsat():
    """p6: True / False / None are three different answers."""
    holes = pigeonhole(6, 5)
    s = Solver(30, holes, conflict_limit=2)
    assert s.solve() is None
    assert solve_resolution(holes, max_conflicts=2)['status'] == 'unknown'
