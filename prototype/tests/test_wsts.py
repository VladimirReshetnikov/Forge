"""The antichain workers. Ported from s1, s3 and s4.

Every test here runs on the standard library alone; that is a property of these
three lanes, not a claim about s2's probabilistic systems or s5/s6's real
algebra, which are not merged into this package.
"""
from itertools import product
import pytest

from forge.wsts import certificates as C
from forge.wsts import nets, orders, search, summaries
from forge.wsts.orders import Antichain, Budget, dickson_leq, higman_leq


# --------------------------------------------------------------------------
# orders: the three things s1, s3 and s4 each wrote separately.
# --------------------------------------------------------------------------
def test_dickson_refuses_to_compare_different_dimensions():
    """A silent zip would drop the third coordinate and call these ordered."""
    with pytest.raises(ValueError):
        dickson_leq((1, 2), (1, 2, 0))


def test_natural_rejects_bool_because_python_says_true_equals_one():
    with pytest.raises(ValueError):
        orders.natural(True)
    assert orders.natural(1) == 1


def test_subsequence_dp_agrees_with_the_greedy_scan_it_replaces():
    """The checker deliberately runs the DP. Cross-check it against greedy."""
    def greedy(s, t):
        it = iter(t)
        return all(any(c == x for x in it) for c in s)

    alphabet = 'ab'
    words = [''.join(w) for n in range(4) for w in product(alphabet, repeat=n)]
    for s in words:
        for t in words:
            assert orders.subsequence(s, t) == greedy(s, t)


def test_antichain_prunes_dominated_elements_and_reports_new_information():
    a = Antichain(dickson_leq)
    assert a.add((2, 2))
    assert not a.add((3, 3))          # already in the upward closure
    assert a.add((1, 5))
    assert a.add((1, 1))              # strictly below (2,2) and (1,5)
    assert sorted(a.elements) == [(1, 1)]
    assert (4, 4) in a
    assert (0, 9) not in a


def test_canonical_rejects_an_unsorted_or_redundant_basis():
    assert C.canonical([(0, 2), (1, 1), (2, 0)], dickson_leq)
    assert not C.canonical([(1, 1), (0, 2)], dickson_leq)      # unsorted
    assert not C.canonical([(0, 2), (1, 3)], dickson_leq)      # dominated


def test_predecessor_is_least_not_merely_sufficient():
    consume, produce, target = (1, 0), (0, 2), (0, 3)
    p = orders.predecessor(consume, produce, target)
    assert p == (1, 1)
    # It fires and covers.
    after = tuple(p[i] - consume[i] + produce[i] for i in range(2))
    assert dickson_leq(target, after)
    # Nothing strictly below it does.
    for i in range(2):
        if p[i] == 0:
            continue
        lower = list(p)
        lower[i] -= 1
        lower = tuple(lower)
        ok = dickson_leq(consume, lower) and dickson_leq(
            target, tuple(lower[j] - consume[j] + produce[j] for j in range(2)))
        assert not ok


# --------------------------------------------------------------------------
# The one antichain three proposals computed independently.
# --------------------------------------------------------------------------
def mutual_exclusion_net() -> nets.Net:
    """Two clients and one lock. Two clients holding it at once is the target.

    s1, s3 and s4 each shipped this net and each computed the same three-element
    frontier. The coordinate ORDER differs between them --- s1 reports
    {(0,0,2),(1,1,1),(2,2,0)} and s4 reports {(0,2,0),(1,1,1),(2,0,2)} --- but
    the bijection between their place orderings carries one onto the other, so
    it is one result reported three times, not three results. It is stated once
    here for exactly that reason.

    Places: 0 idle, 1 lock available, 2 in critical section.
    """
    return nets.Net.from_dict({
        'kind': 'pt-net-coverability',
        'dimension': 3,
        'transitions': [
            {'name': 'enter', 'consume': [1, 1, 0], 'produce': [0, 0, 1]},
            {'name': 'leave', 'consume': [0, 0, 1], 'produce': [1, 1, 0]},
        ],
        'targets': [[0, 0, 2]],
    })


def test_mutual_exclusion_frontier_is_the_three_element_antichain():
    result = search.frontier(mutual_exclusion_net())
    assert result['kind'] == 'frontier'
    basis = [tuple(e['marking']) for e in result['certificate']['basis']]
    assert sorted(basis) == [(0, 0, 2), (1, 1, 1), (2, 2, 0)]
    checked = C.check_frontier(mutual_exclusion_net().to_dict(), result['certificate'])
    assert checked['status'] == 'PYTHON_CHECKED'


def test_the_frontier_decides_markings_it_never_visited():
    """One certificate answers infinitely many initial markings by comparison."""
    certificate = search.frontier(mutual_exclusion_net())['certificate']
    C.check_frontier(mutual_exclusion_net().to_dict(), certificate)
    basis = [tuple(e['marking']) for e in certificate['basis']]

    def unsafe(marking):
        return any(dickson_leq(b, marking) for b in basis)

    assert unsafe((2, 2, 0))          # two clients, one lock, both can enter
    assert unsafe((7, 3, 0))
    assert not unsafe((9, 0, 0))      # no lock was ever available
    assert not unsafe((1, 9, 0))      # only one client exists


# --------------------------------------------------------------------------
# s1: frontiers, run compression, thresholds.
# --------------------------------------------------------------------------
def test_checker_recomputes_summaries_in_the_other_coordinate_system():
    """producer (need, give) and checker (need, delta) must agree via give = need + delta."""
    net = mutual_exclusion_net()
    dag = summaries.RunDAG(net)
    node = dag.seq(dag.step(0), dag.repeat(dag.seq(dag.step(1), dag.step(0)), 5))
    produced = dag.summarize(node)
    nodes, roots = dag.compact([node])
    checked = C.check_runs(net.to_dict(), nodes)
    need, delta, length = checked[roots[0]]
    assert need == produced.need
    assert tuple(need[i] + delta[i] for i in range(3)) == produced.give
    assert length == produced.length == 11


def test_a_repeat_count_of_a_quintillion_costs_nothing():
    net = mutual_exclusion_net()
    dag = summaries.RunDAG(net)
    node = dag.repeat(dag.seq(dag.step(0), dag.step(1)), 10 ** 18)
    nodes, roots = dag.compact([node])
    assert len(nodes) <= 6
    need, delta, length = C.check_runs(net.to_dict(), nodes)[roots[0]]
    assert length == 2 * 10 ** 18
    assert delta == (0, 0, 0)          # enter then leave restores the marking


def test_frontier_certificate_rejects_a_tampered_basis():
    net = mutual_exclusion_net()
    certificate = search.frontier(net)['certificate']
    # Raise one basis element: the basis is no longer minimal, and a marking
    # that really is unsafe would now be reported safe.
    certificate['basis'][0]['marking'][0] += 1
    with pytest.raises(C.InvalidCertificate):
        C.check_frontier(net.to_dict(), certificate)


def test_frontier_certificate_must_be_bound_to_its_own_problem():
    net = mutual_exclusion_net()
    certificate = search.frontier(net)['certificate']
    other = net.to_dict()
    other['targets'] = [[0, 0, 3]]
    with pytest.raises(C.InvalidCertificate):
        C.check_frontier(other, certificate)


def basis_thresholds(frontier, query, d=3):
    """Producer side: least n making each basis element reachable, or None."""
    out = []
    for entry in frontier['basis']:
        b = tuple(entry['marking'])
        if any(query['slope'][i] == 0 and query['offset'][i] < b[i] for i in range(d)):
            out.append(None)
            continue
        n = 0
        while not all(query['offset'][i] + n * query['slope'][i] >= b[i] for i in range(d)):
            n += 1
        out.append(n)
    return out


def test_one_lock_is_safe_for_every_number_of_clients():
    """No n breaks mutual exclusion when the lock count does not scale.

    The frontier settles this for ALL n at once, and the argument is about the
    slope rather than about any particular n: every basis element needs either
    a second lock or a client already inside, and the family (n, 1, 0) supplies
    neither at any n. A checker that tried n = 0, 1, 2, ... would never finish.
    """
    net = mutual_exclusion_net()
    frontier = search.frontier(net)['certificate']
    query = {'problem': net.to_dict(), 'slope': [1, 0, 0], 'offset': [0, 1, 0]}
    thresholds = basis_thresholds(frontier, query)
    assert thresholds == [None, None, None]
    certificate = {'schema': 'forge.wsts.threshold.v1', 'query': query,
                   'frontier': frontier, 'basis_thresholds': thresholds,
                   'threshold': None}
    checked = C.check_threshold(query, certificate)
    assert checked['all_safe']
    assert checked['threshold'] is None


def test_two_clients_with_two_locks_break_mutual_exclusion():
    """Scale the locks with the clients and the answer becomes a number."""
    net = mutual_exclusion_net()
    frontier = search.frontier(net)['certificate']
    query = {'problem': net.to_dict(), 'slope': [1, 1, 0], 'offset': [0, 0, 0]}
    thresholds = basis_thresholds(frontier, query)
    finite = [n for n in thresholds if n is not None]
    certificate = {'schema': 'forge.wsts.threshold.v1', 'query': query,
                   'frontier': frontier, 'basis_thresholds': thresholds,
                   'threshold': min(finite)}
    checked = C.check_threshold(query, certificate)
    assert checked['threshold'] == 2
    assert not checked['all_safe']


def test_a_threshold_that_is_not_least_is_rejected():
    """Feasible is not enough. The checker tests n-1 as well as n."""
    net = mutual_exclusion_net()
    frontier = search.frontier(net)['certificate']
    query = {'problem': net.to_dict(), 'slope': [1, 1, 0], 'offset': [0, 0, 0]}
    inflated = [None if n is None else n + 1
                for n in basis_thresholds(frontier, query)]
    certificate = {'schema': 'forge.wsts.threshold.v1', 'query': query,
                   'frontier': frontier, 'basis_thresholds': inflated,
                   'threshold': min(n for n in inflated if n is not None)}
    with pytest.raises(C.InvalidCertificate):
        C.check_threshold(query, certificate)


# --------------------------------------------------------------------------
# s3: counter systems with infinite initial families.
# --------------------------------------------------------------------------
def producer_consumer() -> dict:
    """A producer fills a buffer; a consumer drains it. Start with n of each."""
    return {
        'kind': 'vass-coverability',
        'controls': 1,
        'dimension': 2,
        'transitions': [
            {'src': 0, 'dst': 0, 'consume': [1, 0], 'produce': [0, 1]},
            {'src': 0, 'dst': 0, 'consume': [0, 1], 'produce': [1, 0]},
        ],
        'bad': [{'control': 0, 'vector': [0, 3]}],
        'initials': [{'control': 0, 'base': [0, 0], 'rays': [[1, 0]]}],
    }


def test_an_infinite_initial_family_is_refuted_by_one_parameter_choice():
    problem = producer_consumer()
    system = nets.Vass(1, 2, tuple(
        nets.Edge(t['src'], t['dst'], tuple(t['consume']), tuple(t['produce']))
        for t in problem['transitions']))
    families = [nets.InitialFamily(f['control'], tuple(f['base']),
                                  tuple(tuple(r) for r in f['rays']))
                for f in problem['initials']]
    result = search.solve_vass(system, [(0, (0, 3))], families)
    assert result['kind'] == 'unsafe'
    certificate = {'schema': 'forge.wsts.unsafe.v1', 'problem': problem,
                   'initial': result['initial'], 'parameters': result['parameters'],
                   'transitions': result['transitions']}
    checked = C.check_counterexample(problem, certificate)
    assert checked['status'] == 'PYTHON_CHECKED'


def test_a_safety_basis_holds_for_every_parameter_at_once():
    """The buffer never holds 3 items when only 2 tokens exist, for ALL n.

    The initial family here has no ray at all, so it is a single marking; the
    point is that the checker establishes it by an argument about the rays,
    not by trying parameter values.
    """
    problem = producer_consumer()
    problem['initials'] = [{'control': 0, 'base': [2, 0], 'rays': []}]
    system = nets.Vass(1, 2, tuple(
        nets.Edge(t['src'], t['dst'], tuple(t['consume']), tuple(t['produce']))
        for t in problem['transitions']))
    result = search.solve_vass(system, [(0, (0, 3))], [
        nets.InitialFamily(0, (2, 0), ())])
    assert result['kind'] == 'safe'
    certificate = {'schema': 'forge.wsts.safe.v1', 'problem': problem,
                   'basis': [[list(v) for v in result['basis'][0]]]}
    checked = C.check_backward_closed(problem, certificate)
    assert checked['status'] == 'PYTHON_CHECKED'


def test_a_counterexample_that_does_not_replay_is_rejected():
    problem = producer_consumer()
    certificate = {'schema': 'forge.wsts.unsafe.v1', 'problem': problem,
                   'initial': 0, 'parameters': [2], 'transitions': [0, 0]}
    # Two producer steps from (2,0) reach (0,2), which does not cover (0,3).
    with pytest.raises(C.InvalidCertificate):
        C.check_counterexample(problem, certificate)


def test_safety_basis_must_actually_be_backward_closed():
    problem = producer_consumer()
    problem['initials'] = [{'control': 0, 'base': [2, 0], 'rays': []}]
    certificate = {'schema': 'forge.wsts.safe.v1', 'problem': problem,
                   'basis': [[[0, 3]]]}          # the bad state alone
    with pytest.raises(C.InvalidCertificate):
        C.check_backward_closed(problem, certificate)


# --------------------------------------------------------------------------
# s4: matrix updates, direct-cover receipts, lossy channels.
# --------------------------------------------------------------------------
def test_a_matrix_update_has_several_incomparable_least_predecessors():
    """A transition that can draw from either of two places.

    This is why nets.py returns a LIST of predecessors. A vector addition
    always has exactly one least predecessor; a matrix update need not, and
    returning one of them would make the backward search unsound.
    """
    t = nets.MatrixTransition(0, 0, (0, 0), ((1, 1), (0, 0)), (0, 0))
    minima = t.minimal_surpluses((2, 0))
    assert minima == [(0, 2), (1, 1), (2, 0)]
    assert all(not dickson_leq(a, b) for a in minima for b in minima if a != b)


def test_direct_cover_receipt_certifies_a_region_without_listing_it():
    """A cover of every predecessor, checked as a partition of a box."""
    matrix = ((1, 1), (0, 0))
    consume, produce, target = (0, 0), (0, 0), (2, 0)
    basis = [[0, 0]]                   # everything is covered by the origin
    receipt = {'kind': 'direct-cover', 'caps': [2, 2],
               'tree': ['basis', 0]}
    checked = C.check_direct_cover(matrix, consume, produce, target, basis, receipt)
    assert checked['status'] == 'PYTHON_CHECKED'
    assert checked['box_volume'] == 9


def test_direct_cover_rejects_a_partition_with_a_hole():
    """A tree that tiles less than its declared box proves nothing about the gap."""
    matrix = ((1, 0), (0, 1))
    consume, produce, target = (0, 0), (0, 0), (1, 1)
    basis = [[1, 1]]
    # Splits coordinate 0 at 0 but then claims only the left half.
    receipt = {'kind': 'direct-cover', 'caps': [1, 1],
               'tree': ['split', 0, 0, ['impossible', 0], ['impossible', 0]]}
    with pytest.raises(C.InvalidCertificate):
        C.check_direct_cover(matrix, consume, produce, target, basis, receipt)


def test_direct_cover_rejects_a_false_infeasibility_leaf():
    matrix = ((1, 0), (0, 1))
    consume, produce, target = (0, 0), (0, 0), (1, 1)
    basis = [[0, 0]]
    receipt = {'kind': 'direct-cover', 'caps': [1, 1], 'tree': ['impossible', 0]}
    with pytest.raises(C.InvalidCertificate):
        C.check_direct_cover(matrix, consume, produce, target, basis, receipt)


def test_lossy_channels_need_no_loss_rule_because_the_order_is_the_loss():
    """A send-transition protocol, closed under the subsequence order.

    Nothing in the model or the checker mentions message loss. It does not have
    to: the basis element 'a' at control 1 stands for EVERY word containing an
    'a', so 'ba', 'aab' and 'bbbab' are all in the set already, and dropping
    symbols from any of them lands somewhere still in it. The loss semantics is
    the order, not an extra rule.
    """
    transitions = [{'src': 0, 'dst': 1, 'op': 'send', 'channel': 0, 'symbol': 'a'}]
    bad = [{'control': 1, 'words': ['aa']}]
    # Control 1 needs an 'a'; control 0 reaches that by sending, from anything.
    basis = [[['']], [['a']]]
    checked = C.check_lossy_closed(2, ['a', 'b'], transitions, bad, basis)
    assert checked['status'] == 'PYTHON_CHECKED'
    # The loss closure, never written down anywhere, holds anyway.
    for word in ('a', 'ba', 'aab', 'bbbab'):
        assert higman_leq(('a',), (word,))


def test_lossy_basis_that_misses_a_bad_configuration_is_rejected():
    transitions = [{'src': 0, 'dst': 0, 'op': 'send', 'channel': 0, 'symbol': 'a'}]
    bad = [{'control': 0, 'words': ['b']}]
    basis = [[['a']]]
    with pytest.raises(C.InvalidCertificate):
        C.check_lossy_closed(1, ['a', 'b'], transitions, bad, basis)


def test_lossy_search_and_checker_agree_on_a_two_control_protocol():
    transitions = [
        nets.ChannelTransition(0, 1, 'send', 0, 'a'),
        nets.ChannelTransition(1, 0, 'recv', 0, 'a'),
    ]
    result = search.solve_lossy(2, transitions, [(1, ('a',))], [(0, ('',))])
    assert result['kind'] == 'unsafe'


# --------------------------------------------------------------------------
# The separation the package claims, checked rather than asserted.
# --------------------------------------------------------------------------
def test_the_checker_module_imports_no_search_code():
    """Stated in the docstring; verified here, because a docstring cannot fail.

    Parsed rather than grepped: the docstring itself contains the words, and a
    substring scan would be satisfied by the prose that promises the property.
    That is the same mistake this repository's own Lean sorry-scanner made.
    """
    import ast
    import forge.wsts.certificates as module
    tree = ast.parse(open(module.__file__, encoding='utf-8').read())
    imported = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            imported.add(node.module.lstrip('.'))
        elif isinstance(node, ast.Import):
            imported.update(alias.name for alias in node.names)
    assert 'search' not in imported
    assert 'summaries' not in imported
    assert imported <= {'__future__', 'typing', 'orders', 'nets'}


def test_budget_exhaustion_is_unknown_and_never_safe():
    """An unbounded producer loop: the basis grows without settling in time."""
    system = nets.Vass(1, 1, (nets.Edge(0, 0, (0,), (1,)),))
    result = search.solve_vass(
        system, [(0, (5,))], [nets.InitialFamily(0, (0,), ())],
        budget=Budget(admissions=2, predecessors=2))
    assert result['kind'] in ('unknown', 'safe')
    if result['kind'] == 'unknown':
        assert result['reason'] == 'budget'
