"""Greatest invariant-generator subspace with degree-bounded ideal multipliers.

For W within the degree-d template, define J_e(W)=span{m*p : deg(m)<=e,p in W}.
Descending W <- W intersect pullback(T)^-1(J_e(W)) is linear at each step.
This avoids simultaneously solving bilinear unknown generators and multipliers.
Certificates contain polynomial multiplier matrices; the checker only expands
identities. It does not check maximality of the returned generator space.
"""
import exact as ex
from invariant_space import encode_problem


def products(space, n, multiplier_degree):
    mons = [{m: ex.Q(1)} for m in ex.monomials(n, multiplier_degree)]
    return mons, [ex.mul(m, p) for p in space for m in mons]


def synthesize(n, degree, multiplier_degree, initial_maps, transitions):
    if (type(multiplier_degree) is not int or multiplier_degree < 0 or
        not initial_maps or any(len(m) != n for m in initial_maps + transitions)):
        raise ValueError('invalid degree or map arity')
    basis = [{m: ex.Q(1)} for m in ex.monomials(n, degree)]
    constraints = []
    for init in initial_maps:
        constraints += ex.coefficient_rows([ex.compose(p, init) for p in basis])
    space = ex.poly_basis([ex.linear_combination(c, basis)
                          for c in ex.nullspace(constraints, len(basis))])
    dimensions, restrictions = [len(space)], 0
    while space:
        old_dimension = len(space)
        for transition in transitions:
            d = len(space)
            _, ideal_products = products(space, n, multiplier_degree)
            pullbacks = [ex.compose(p, transition) for p in space]
            columns = pullbacks + [ex.scale(-1, p) for p in ideal_products]
            kernel = ex.nullspace(ex.coefficient_rows(columns), len(columns))
            space = ex.poly_basis([ex.linear_combination(c[:d], space) for c in kernel])
            restrictions += 1
            if not space:
                break
        dimensions.append(len(space))
        if len(space) == old_dimension:
            break
    mons, ideal_products = products(space, n, multiplier_degree)
    matrices = []
    for transition in transitions:
        matrix = []
        for p in space:
            coefficients = ex.coordinates(ex.compose(p, transition), ideal_products)
            if coefficients is None:
                raise AssertionError('internal ideal closure failure')
            row = [ex.linear_combination(coefficients[j*len(mons):(j+1)*len(mons)], mons)
                   for j in range(len(space))]
            matrix.append([ex.encode_poly(q) for q in row])
        matrices.append(matrix)
    problem = encode_problem(n, degree, initial_maps, transitions)
    problem['multiplier_degree'] = multiplier_degree
    cert = {'schema': 'forge.ideal-space/1', 'problem': problem,
            'invariants': [ex.encode_poly(p) for p in space], 'matrices': matrices}
    return cert, {'template_dimension': len(basis), 'dimensions': dimensions,
                  'restrictions': restrictions, 'invariant_dimension': len(space),
                  'multiplier_degree': multiplier_degree}


def check(problem, certificate):
    try:
        if (certificate.get('schema') != 'forge.ideal-space/1' or
                certificate.get('problem') != problem):
            return False
        n, d, e = problem['variables'], problem['degree'], problem['multiplier_degree']
        if (any(type(a) is not int for a in [n, d, e]) or n < 1 or d < 0 or e < 0):
            return False
        initial = [[ex.decode_poly(p, n) for p in m] for m in problem['initial']]
        transitions = [[ex.decode_poly(p, n) for p in m] for m in problem['transitions']]
        if not initial or any(len(m) != n for m in initial + transitions):
            return False
        ps = [ex.decode_poly(p, n) for p in certificate['invariants']]
        if any(sum(m) > d for p in ps for m in p):
            return False
        if any(ex.compose(p, init) for p in ps for init in initial):
            return False
        matrices = certificate['matrices']
        if len(matrices) != len(transitions):
            return False
        for transition, matrix in zip(transitions, matrices):
            if len(matrix) != len(ps):
                return False
            for p, row in zip(ps, matrix):
                if len(row) != len(ps):
                    return False
                hs = [ex.decode_poly(h, n) for h in row]
                if any(sum(m) > e for h in hs for m in h):
                    return False
                rhs = {}
                for h, q in zip(hs, ps):
                    rhs = ex.add(rhs, ex.mul(h, q))
                if ex.compose(p, transition) != rhs:
                    return False
        return True
    except (KeyError, TypeError, ValueError, IndexError, ZeroDivisionError, AttributeError):
        return False
