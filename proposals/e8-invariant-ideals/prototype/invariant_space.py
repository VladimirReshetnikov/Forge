"""Greatest pullback-stable subspace, with a search-free identity checker."""
from exact import (Q, const, compose, monomials, nullspace, coefficient_rows,
                   linear_combination, poly_basis, coordinates, encode_poly,
                   decode_poly, scale)


def synthesize(n, degree, initial_maps, transitions):
    """All maps are polynomial substitutions; all transition choices are enabled.

    Returns the greatest subspace inside the supplied degree template whose
    members vanish initially and whose pullbacks remain in that subspace.
    The initial maps range over all rational parameter values.
    """
    if not initial_maps or any(len(m) != n for m in initial_maps + transitions):
        raise ValueError('invalid map arity or missing initial map')
    basis = [{m: Q(1)} for m in monomials(n, degree)]
    constraints = []
    for init in initial_maps:
        constraints += coefficient_rows([compose(p, init) for p in basis])
    space = poly_basis([linear_combination(c, basis)
                        for c in nullspace(constraints, len(basis))])
    dimensions = [len(space)]
    restrictions = 0
    while space:
        old_dimension = len(space)
        for transition in transitions:
            d = len(space)
            pullbacks = [compose(p, transition) for p in space]
            columns = pullbacks + [scale(-1, p) for p in space]
            kernel = nullspace(coefficient_rows(columns), 2 * d)
            space = poly_basis([linear_combination(c[:d], space) for c in kernel])
            restrictions += 1
            if not space:
                break
        dimensions.append(len(space))
        if len(space) == old_dimension:
            break
    matrices = []
    for transition in transitions:
        matrix = [coordinates(compose(p, transition), space) for p in space]
        if any(c is None for c in matrix):
            raise AssertionError('internal closure failure')
        matrices.append([[[c.numerator, c.denominator] for c in row] for row in matrix])
    problem = encode_problem(n, degree, initial_maps, transitions)
    certificate = {'schema': 'forge.pullback-space/1', 'problem': problem,
                   'invariants': [encode_poly(p) for p in space],
                   'matrices': matrices}
    return certificate, {'template_dimension': len(basis), 'dimensions': dimensions,
                         'restrictions': restrictions, 'invariant_dimension': len(space)}


def encode_problem(n, degree, initial_maps, transitions):
    return {'variables': n, 'degree': degree,
            'initial': [[encode_poly(p) for p in m] for m in initial_maps],
            'transitions': [[encode_poly(p) for p in m] for m in transitions]}


def check(problem, certificate):
    """No synthesis, Gaussian elimination, invariant discovery, or sampling.

    This checks soundness of the returned packet, NOT maximality of its span.
    The problem parameter must come from the caller's trusted reification.
    """
    try:
        if (certificate.get('schema') != 'forge.pullback-space/1' or
                certificate.get('problem') != problem):
            return False
        n, degree = problem['variables'], problem['degree']
        if type(n) is not int or n < 1 or type(degree) is not int or degree < 0:
            return False
        initial = [[decode_poly(p, n) for p in m] for m in problem['initial']]
        transitions = [[decode_poly(p, n) for p in m] for m in problem['transitions']]
        if not initial or any(len(m) != n for m in initial + transitions):
            return False
        inv = [decode_poly(p, n) for p in certificate['invariants']]
        if any(sum(e) > degree for p in inv for e in p):
            return False
        matrices = certificate['matrices']
        if len(matrices) != len(transitions):
            return False
        if any(compose(p, init) for p in inv for init in initial):
            return False
        for transition, matrix in zip(transitions, matrices):
            if len(matrix) != len(inv):
                return False
            for p, row in zip(inv, matrix):
                if len(row) != len(inv):
                    return False
                cs = []
                for pair in row:
                    if (type(pair) is not list or len(pair) != 2 or
                        any(type(a) is not int for a in pair) or pair[1] <= 0):
                        return False
                    c = Q(*pair)
                    if [c.numerator, c.denominator] != pair:
                        return False
                    cs.append(c)
                if compose(p, transition) != linear_combination(cs, inv):
                    return False
        return True
    except (KeyError, TypeError, ValueError, IndexError, ZeroDivisionError, AttributeError):
        return False
