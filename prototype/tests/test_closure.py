"""The closure workers. Ported from e4, e5, e6, e8 and e9.

Every test in this file runs on the standard library alone; that is a property
of these five lanes, not a claim about the ideal or telescoping lanes, which
are not merged into this package.
"""
from fractions import Fraction as Q
from itertools import product
import random
import pytest

from forge.closure import certificates as C
from forge.closure import cover, kripke, ore, projection, words


# --------------------------------------------------------------------------
# e5 / e6 / e9: observable-space closure and separating words.
# --------------------------------------------------------------------------
def test_conservation_gap_is_not_a_conserved_quantity():
    """2x - y is zero after every word, but its value doubles each step.

    A worker that only looks for invariants with q' = q finds nothing here.
    """
    model = words.conservation_gap_model()
    result = words.search(model)
    assert result['status'] == 'closure'
    assert result['stats']['basis_size'] == 1
    assert C.check_observable(model, result['certificate'])
    # The observation really does double rather than stay put.
    step = words.vec_mat(model.output, model.actions[1])
    assert step == tuple(2*c for c in model.output)


@pytest.mark.parametrize('dimension', [2, 3, 5, 8, 13, 24])
def test_shift_family_attains_the_separating_bound(dimension):
    """Correct on every input shorter than D-1, wrong at exactly D-1."""
    model = words.shift_model(dimension)
    result = words.search(model)
    assert result['status'] == 'separating'
    assert len(result['word']) == dimension - 1
    assert C.check_separating_word(model, result['word'], result['value'])
    # Every strictly shorter word observes zero, which is why testing a fixed
    # prefix classifies these as correct.
    for length in range(dimension - 1):
        for word in product(range(len(model.actions)), repeat=length):
            assert model.evaluate(word) == 0


def test_separating_word_is_replayed_in_the_original_matrices():
    model = words.shift_model(4)
    result = words.search(model)
    assert model.evaluate(result['word']) == result['value'] != 0
    # A different word of the same length is not a counterexample.
    assert not C.check_separating_word(model, [0, 0], result['value'])


def _block_model(first, second, initial_a, initial_b, out_a, out_b):
    """Compare two machines by one zero-observation goal on their product."""
    da, db = len(initial_a), len(initial_b)
    rows = ([tuple(list(row) + [Q(0)]*db) for row in first] +
            [tuple([Q(0)]*da + list(row)) for row in second])
    return words.Model.build(
        da+db, list(initial_a) + list(initial_b),
        list(out_a) + [-c for c in out_b], (tuple(rows),))


def test_equivalence_by_product_construction():
    """Equal output needs neither equal state dimensions nor equal coordinates.

    Both machines count steps, one in a single coordinate and one in a scaled
    pair. A structural comparison of the state vectors fails; observable
    closure finds the combination that settles the outputs.
    """
    first = ((Q(1), Q(1)), (Q(0), Q(1)))             # (c, 1) -> (c+1, 1)
    second = ((Q(1), Q(2)), (Q(0), Q(1)))            # (d, 1) -> (d+2, 1)
    same = _block_model(first, first, (Q(0), Q(1)), (Q(0), Q(1)),
                        (Q(1), Q(0)), (Q(1), Q(0)))
    result = words.search(same)
    assert result['status'] == 'closure'
    assert C.check_observable(same, result['certificate'])

    different = _block_model(first, second, (Q(0), Q(1)), (Q(0), Q(1)),
                             (Q(1), Q(0)), (Q(1), Q(0)))
    result = words.search(different)
    assert result['status'] == 'separating'
    assert C.check_separating_word(different, result['word'], result['value'])
    # The first step already separates them: one counts by 1, the other by 2.
    assert len(result['word']) == 1


def test_target_membership_equation_is_indispensable():
    """A valid invariant basis that does not span the target proves nothing."""
    model = words.conservation_gap_model()
    result = words.search(model)
    cert = dict(result['certificate'])
    cert['target_coordinates'] = [Q(0)]*len(cert['target_coordinates'])
    assert not C.check_observable(model, cert)


def test_redundant_rows_are_still_a_valid_certificate():
    """The checker does not verify independence, minimality, or provenance."""
    model = words.conservation_gap_model()
    cert = dict(words.search(model)['certificate'])
    basis = [list(r) for r in cert['basis']]
    doubled = basis + [[2*c for c in basis[0]]]
    actions = []
    for a in cert['actions']:
        rows = [list(r) + [Q(0)] for r in a]
        rows.append([Q(0)]*len(a) + [Q(2)])
        actions.append(rows)
    extended = {'kind': 'observable-closure', 'basis': doubled,
                'target_coordinates': list(cert['target_coordinates']) + [Q(0)],
                'actions': actions}
    assert C.check_observable(model, extended)


@pytest.mark.parametrize('field', ['basis', 'actions'])
def test_observable_mutations_are_rejected(field):
    model = words.conservation_gap_model()
    cert = {k: v for k, v in words.search(model)['certificate'].items()}
    if field == 'basis':
        cert['basis'] = [[c + 1 for c in cert['basis'][0]]]
    else:
        cert['actions'] = [[[c + 1 for c in row] for row in a]
                           for a in cert['actions']]
    assert not C.check_observable(model, cert)


def test_floats_are_rejected_rather_than_coerced():
    with pytest.raises(TypeError):
        words.rational(0.5)
    with pytest.raises(TypeError):
        words.rational(True)
    with pytest.raises(ValueError):
        words.rational([1, 0])


# --------------------------------------------------------------------------
# e8: finite-algebra covers.
# --------------------------------------------------------------------------
@pytest.mark.parametrize('modulus', range(1, 13))
def test_leaf_and_node_counts_cover_every_modulus(modulus):
    problem = cover.binary_tree_counts(modulus)
    certificate, stats = cover.synthesize(problem)
    assert certificate['kind'] == 'cover'
    assert len(certificate['cover']) == modulus
    assert C.check_cover(problem, certificate)


def test_recorded_counts_for_modulus_twelve():
    """Three different quantities, and they are not interchangeable.

    The explicit product has 144 states and 20,736 binary table entries; the
    search reaches 12 states and evaluates 145 distinct tuples. Building and
    validating the whole table still costs work proportional to 20,736.
    """
    problem = cover.binary_tree_counts(12)
    assert problem['states'] == 144
    assert len(problem['constructors'][1]['table']) == 144*144
    _, stats = cover.synthesize(problem)
    assert stats['states_reached'] == 12
    assert stats['evaluations'] == 145
    assert stats['tuple_visits'] == 235


def test_mirror_fold_needs_commutativity_not_associativity():
    commutative = [[0, 1], [1, 0]]                 # XOR: commutes, not needed to
    certificate, _ = cover.synthesize(cover.mirror_problem(commutative))
    assert certificate['kind'] == 'cover'
    assert C.check_cover(cover.mirror_problem(commutative), certificate)

    # Left projection: associative but not commutative.
    associative = [[0, 0], [1, 1]]
    problem = cover.mirror_problem(associative)
    certificate, _ = cover.synthesize(problem)
    assert certificate['kind'] == 'counterexample'
    assert C.check_cover(problem, certificate)


def test_counterexample_tree_requires_earlier_child_indices():
    problem = cover.mirror_problem([[0, 0], [1, 1]])
    certificate, _ = cover.synthesize(problem)
    broken = dict(certificate)
    broken['nodes'] = [dict(n) for n in certificate['nodes']]
    broken['nodes'][-1] = dict(broken['nodes'][-1],
                               children=[len(broken['nodes'])-1])
    assert not C.check_cover(problem, broken)


def test_a_good_state_is_not_a_counterexample():
    problem = cover.binary_tree_counts(5)
    certificate, _ = cover.synthesize(problem)
    forged = {'schema': cover.SCHEMA, 'kind': 'counterexample',
              'problem': problem,
              'nodes': [{'constructor': 0, 'children': []}], 'root': 0}
    assert not C.check_cover(problem, forged)


def test_a_cover_leaving_the_good_set_is_rejected():
    problem = cover.binary_tree_counts(4)
    certificate, _ = cover.synthesize(problem)
    bad = dict(certificate,
               cover=sorted(set(certificate['cover']) | {problem['states']-1}))
    assert not C.check_cover(problem, bad)


def test_unknown_is_not_a_certificate():
    problem = cover.binary_tree_counts(9)
    certificate, _ = cover.synthesize(problem, budget=3)
    assert certificate['kind'] == 'unknown'
    assert not C.check_cover(problem, certificate)


# --------------------------------------------------------------------------
# e8: exact one-output integer projection.
# --------------------------------------------------------------------------
def test_large_period_program_is_small():
    """A 60-bit period in 42 nodes, and the recorded witness at x = 0."""
    problem = projection.large_period_example()
    certificate = projection.synthesize(problem)
    program = certificate['program']
    assert program['period'] == 1_000_000_016_000_000_063
    assert len(program['nodes']) == 42
    assert C.check_projection(problem, certificate)
    feasible, witness = projection.evaluate(program, [0])
    assert feasible and witness == 2_000_000_015
    assert projection.holds(problem, [0], witness)


@pytest.mark.parametrize('x', [0, 1, -1, 10**100, -10**100])
def test_large_period_witness_at_extreme_parameters(x):
    problem = projection.large_period_example()
    program = projection.synthesize(problem)['program']
    feasible, witness = projection.evaluate(program, [x])
    assert feasible
    assert projection.holds(problem, [x], witness)


def test_negative_coefficient_lower_bounds_use_the_right_rounding():
    """ceil(-b/c) = -floor(b/c). Truncation toward zero is wrong below zero."""
    problem = {'parameters': 1,
               'inequalities': [{'a': -2, 'rhs': [0, 1]}],
               'congruences': []}
    program = projection.synthesize(problem)['program']
    for x in range(-9, 10):
        feasible, witness = projection.evaluate(program, [x])
        assert feasible and projection.holds(problem, [x], witness)


def test_guard_agrees_with_an_exhaustive_concrete_oracle():
    """The oracle is complete for these inputs, by a stated range argument.

    Let B be one more than the largest absolute right side and P the lcm of the
    moduli. Every finite endpoint lies in [-B, B] and the congruence solution
    set has period dividing P, so a satisfiable problem has a witness inside
    [-B-P, B+P]. Enumerating that range is complete here -- not an arbitrary
    small box, and not a proof about the generator.
    """
    rng = random.Random(20260915)
    feasible_count = infeasible_count = 0
    for _ in range(120):
        parameters = rng.choice([1, 2])
        problem = {
            'parameters': parameters,
            'inequalities': [
                {'a': rng.choice([-4, -3, -2, -1, 1, 2, 3, 4]),
                 'rhs': [rng.randint(-4, 4) for _ in range(parameters+1)]}
                for _ in range(rng.randint(0, 3))],
            'congruences': [
                {'a': rng.choice([-4, -3, -2, -1, 1, 2, 3, 4]),
                 'rhs': [rng.randint(-4, 4) for _ in range(parameters+1)],
                 'm': rng.randint(1, 8)}
                for _ in range(rng.randint(0, 3))]}
        certificate = projection.synthesize(problem)
        assert C.check_projection(problem, certificate)
        program = certificate['program']
        bound = 1 + max([abs(v) for row in problem['inequalities'] + problem['congruences']
                         for v in row['rhs']] + [0])
        period = 1
        for row in problem['congruences']:
            g = period
            n = row['m']
            while n:
                g, n = n, g % n
            period = period*row['m']//g
        for xs in product([-4, -1, 0, 2, 5], repeat=parameters):
            claimed, witness = projection.evaluate(program, list(xs))
            span = bound + period + max(abs(x) for x in xs)*5
            truth = any(projection.holds(problem, list(xs), y)
                        for y in range(-span, span+1))
            assert claimed == truth
            if claimed:
                assert projection.holds(problem, list(xs), witness)
                feasible_count += 1
            else:
                infeasible_count += 1
    assert feasible_count and infeasible_count


def test_bezout_receipt_conditions_are_what_is_checked():
    assert projection.valid_bezout(6, 15, [3, -2, 1])
    assert not projection.valid_bezout(6, 15, [3, -2, 2])      # wrong combination
    assert not projection.valid_bezout(6, 15, [1, -2, 1])      # not a common divisor
    assert not projection.valid_bezout(6, 15, [-3, 2, -1])     # not positive
    assert not projection.valid_bezout(6, 15, [3.0, -2, 1])    # not an integer


def test_projection_mutations_are_rejected():
    problem = projection.large_period_example()
    certificate = projection.synthesize(problem)
    changed = dict(certificate)
    changed['bezout'] = [list(r) for r in certificate['bezout']]
    changed['bezout'][0] = [changed['bezout'][0][0], changed['bezout'][0][1]+1,
                            changed['bezout'][0][2]]
    assert not C.check_projection(problem, changed)

    moved = dict(certificate)
    moved['program'] = dict(certificate['program'],
                            witness=certificate['program']['witness']-1)
    assert not C.check_projection(problem, moved)

    # A guard cannot be deleted to make an infeasible instance look feasible.
    infeasible = {'parameters': 0, 'inequalities': [],
                  'congruences': [{'a': 2, 'rhs': [1], 'm': 4}]}
    cert = projection.synthesize(infeasible)
    assert not projection.evaluate(cert['program'], [])[0]
    stripped = dict(cert, program=dict(cert['program'], guards=[]))
    assert not C.check_projection(infeasible, stripped)


# --------------------------------------------------------------------------
# e4: finite Kripke countermodels.
# --------------------------------------------------------------------------
@pytest.mark.parametrize('name,problem', [
    ('excluded middle', kripke.EXCLUDED_MIDDLE),
    ('double negation', kripke.DOUBLE_NEGATION),
    ('Peirce', kripke.PEIRCE),
    ('linearity', kripke.LINEARITY),
    ('weak excluded middle', kripke.WEAK_EM),
])
def test_classical_tautologies_are_refuted_constructively(name, problem):
    """Each is classically valid, which is the point.

    An interface turning any of these countermodels into a proof of the negated
    Lean formula would be visibly unsound. These are enforcement tests.
    """
    result = kripke.find_countermodel(problem, max_worlds=3)
    assert result['status'] == 'countermodel', name
    assert kripke.verify(problem, result['certificate'])


def test_linearity_needs_a_branching_model():
    """No chain refutes it, at any length."""
    result = kripke.find_countermodel(kripke.LINEARITY, max_worlds=3)
    relation = result['certificate']['relation']
    n = result['certificate']['worlds']
    incomparable = [(i, j) for i in range(n) for j in range(n)
                    if i != j and not relation[i][j] and not relation[j][i]]
    assert incomparable


@pytest.mark.parametrize('goal', [
    kripke.imp(kripke.atom('P'), kripke.atom('P')),
    kripke.imp(kripke.conj(kripke.atom('P'), kripke.atom('Q')), kripke.atom('P')),
    kripke.imp(kripke.atom('P'), kripke.disj(kripke.atom('P'), kripke.atom('Q'))),
    kripke.imp(kripke.bot(), kripke.atom('P')),
])
def test_valid_schemas_return_unknown_not_a_refutation(goal):
    """Positive controls against an invalid refuter, not theorems proved."""
    result = kripke.find_countermodel(kripke.sequent(goal), max_worlds=3)
    assert result['status'] == 'unknown'
    assert 'no validity claim' in result['reason']


def test_implication_is_checked_at_every_successor():
    """Checking only the current world would make the semantics classical."""
    problem = kripke.EXCLUDED_MIDDLE
    result = kripke.find_countermodel(problem, max_worlds=3)
    certificate = result['certificate']
    # P is false at the root and true somewhere above it: that is exactly why
    # the root forces neither P nor not-P.
    values = certificate['valuation']['P']
    assert not values[certificate['root']]
    assert any(values)


def test_countermodel_mutations_are_rejected():
    problem = kripke.EXCLUDED_MIDDLE
    certificate = kripke.find_countermodel(problem, max_worlds=3)['certificate']
    n = certificate['worlds']

    broken_order = dict(certificate,
                        relation=[[False]*n for _ in range(n)])
    assert not kripke.verify(problem, broken_order)

    broken_persistence = dict(
        certificate,
        valuation={k: [not v for v in vs]
                   for k, vs in certificate['valuation'].items()})
    assert not kripke.verify(problem, broken_persistence)

    wrong_root = dict(certificate, root=n-1) if n > 1 else None
    if wrong_root is not None:
        # Only rejected when the last world is not also least; for the chain
        # fixture it forces P at the root, so the goal becomes forced.
        assert not kripke.verify(problem, wrong_root)


def test_a_solver_supplied_truth_table_is_not_accepted():
    """The certificate schema has no place to put one."""
    problem = kripke.EXCLUDED_MIDDLE
    certificate = dict(kripke.find_countermodel(problem, max_worlds=3)['certificate'])
    certificate['truth'] = {'P': [False, False]}
    assert not kripke.verify(problem, certificate)


# --------------------------------------------------------------------------
# e9: Ore transport and singularity seed plans.
# --------------------------------------------------------------------------
def test_shift_does_not_commute_with_its_coefficient():
    """E*n = (n+1)*E. Commutative multiplication is a different operator."""
    e_times_n = ore.ore_mul([ore.poly(0), ore.poly(1)], [ore.poly(0, 1)])
    assert e_times_n == [(), ore.poly(1, 1)]
    n_times_e = ore.ore_mul([ore.poly(0, 1)], [ore.poly(0), ore.poly(1)])
    assert n_times_e == [(), ore.poly(0, 1)]
    assert e_times_n != n_times_e


def test_worked_common_left_multiple():
    """A = E - (n+1), B = E - 2(n+1) share L = E^2 - 3(n+2)E + 2(n+1)(n+2)."""
    a = [ore.poly(-1, -1), ore.poly(1)]
    b = [ore.poly(-2, -2), ore.poly(1)]
    certificate, stats = ore.common_left_multiple(a, b, 1, 1)
    assert certificate is not None
    assert certificate['common'] == [ore.poly(4, 6, 2), ore.poly(-6, -3), ore.poly(1)]
    assert C.check_ore({'left': a, 'right': b}, certificate)


def test_a_commutative_expansion_is_rejected():
    a = [ore.poly(-1, -1), ore.poly(1)]
    b = [ore.poly(-2, -2), ore.poly(1)]
    certificate, _ = ore.common_left_multiple(a, b, 1, 1)
    forged = dict(certificate)
    # The middle coefficient a commuting indeterminate would produce.
    forged['common'] = [ore.poly(4, 6, 2), ore.poly(-3, -3), ore.poly(1)]
    assert not C.check_ore({'left': a, 'right': b}, forged)


def test_ore_mutation_is_rejected():
    a = [ore.poly(-1, -1), ore.poly(1)]
    b = [ore.poly(-2, -2), ore.poly(1)]
    certificate, _ = ore.common_left_multiple(a, b, 1, 1)
    bumped = dict(certificate)
    bumped['common'] = list(certificate['common'][:-1]) + [ore.poly(2)]
    assert not C.check_ore({'left': a, 'right': b}, bumped)


def test_missed_singularity_countermodel():
    """(n-5)(f(n+1) - 2f(n)) = 0 has two solutions agreeing at 0..5."""
    operator = ore.missed_singularity_example()

    def g(n):
        return 0 if n < 6 else 2**(n-6)

    for n in range(0, 12):
        assert (n-5)*(g(n+1) - 2*g(n)) == 0
    assert all(g(n) == 0 for n in range(6))
    assert g(6) == 1

    plan = ore.singularity_cover(operator)
    assert plan['singular_indices'] == [5]
    assert plan['seed_indices'] == [0, 6]
    assert C.check_singularity_plan({'operator': operator}, plan)


def test_seed_at_s_rather_than_s_plus_r_is_an_off_by_order_error():
    operator = ore.missed_singularity_example()
    plan = dict(ore.singularity_cover(operator))
    plan['seed_indices'] = [0, 5]
    assert not C.check_singularity_plan({'operator': operator}, plan)


def test_an_understated_root_bound_is_rejected():
    operator = ore.missed_singularity_example()
    plan = dict(ore.singularity_cover(operator))
    plan['bound'] = 2
    assert not C.check_singularity_plan({'operator': operator}, plan)


def test_repeated_roots_do_not_duplicate_seed_obligations():
    #  (n-3)^2 as a leading coefficient, order two.
    square = ore.pmul(ore.poly(-3, 1), ore.poly(-3, 1))
    operator = [ore.poly(1), ore.poly(0), square]
    plan = ore.singularity_cover(operator)
    assert plan['singular_indices'] == [3]
    assert plan['seed_indices'] == [0, 1, 5]
    assert C.check_singularity_plan({'operator': operator}, plan)


def test_third_order_with_three_natural_roots():
    leading = ore.pmul(ore.pmul(ore.poly(0, 1), ore.poly(-1, 1)), ore.poly(-5, 1))
    operator = [ore.poly(1), ore.poly(0), ore.poly(0), leading]
    plan = ore.singularity_cover(operator)
    assert plan['singular_indices'] == [0, 1, 5]
    assert plan['seed_indices'] == [0, 1, 2, 3, 4, 8]
    assert C.check_singularity_plan({'operator': operator}, plan)


def test_constant_leading_coefficient_has_no_roots():
    operator = [ore.poly(1), ore.poly(7)]
    plan = ore.singularity_cover(operator)
    assert plan['bound'] == 0 and plan['singular_indices'] == []
    assert plan['seed_indices'] == [0]
    assert C.check_singularity_plan({'operator': operator}, plan)


# --------------------------------------------------------------------------
# The whole subpackage is standard library only, search included.
# --------------------------------------------------------------------------
def test_no_third_party_import_anywhere_in_the_subpackage():
    imported = _imports_of_closure()
    for module in ('numpy', 'scipy', 'sympy'):
        offenders = [n for n in imported
                     if n == module or n.startswith(module + '.')]
        assert not offenders, '%s reached from %s' % (module, offenders)


def _imports_of_closure():
    import ast
    import pathlib
    root = pathlib.Path(__file__).resolve().parents[1] / 'forge' / 'closure'
    names = []
    for path in sorted(root.glob('*.py')):
        tree = ast.parse(path.read_text(encoding='utf-8'))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                names += [a.name for a in node.names]
            elif isinstance(node, ast.ImportFrom) and node.module and node.level == 0:
                names.append(node.module)
    return names
