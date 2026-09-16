"""Sparse Reynolds projection proposer; polynomial orbits, never group enumeration."""
from collections import deque
from fractions import Fraction
from .producer import validate_problem, action, SearchLimit

def project_certificate(problem, terms, *, max_monomials=100_000):
    n, generators = validate_problem(problem)
    source = {tuple(e):Fraction(a,b) for e,a,b in terms}
    unseen = set(source)
    orbits, output, total = [], {}, 0
    while unseen:
        root = min(unseen)
        points, indices, tree = [root], {root:0}, [[list(root), None, None]]
        queue = deque([root])
        while queue:
            exponent = queue.popleft()
            for j,g in enumerate(generators):
                new = action(g, exponent)
                if new not in indices:
                    total += 1
                    if total + len(orbits) + 1 > max_monomials:
                        raise SearchLimit('monomial-orbit budget exceeded')
                    indices[new] = len(points); points.append(new)
                    tree.append([list(new), indices[exponent], j]); queue.append(new)
        average = sum((source.get(e, Fraction()) for e in points), Fraction()) / len(points)
        if average:
            output.update({e:average for e in points})
        unseen.difference_update(points)
        orbits.append(tree)
    return {'format':'forge.symmetry.reynolds.v1', 'orbits':orbits,
            'output':[[list(e),q.numerator,q.denominator] for e,q in sorted(output.items())]}
