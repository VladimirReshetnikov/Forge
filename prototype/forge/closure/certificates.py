# PROVENANCE: the acceptance paths of e4, e5, e6, e8 and e9, collected here so
# that the checking code in this subpackage is separable from the search code
# by inspection as well as by import.
"""Exact certificate CHECKING for the closure workers. No search code here.

Each function takes the AUTHORITATIVE problem separately from the certificate,
so a certificate can never silently replace the problem it claims to be about.

Three of these run a genuinely different computation from their producers:
`check_observable` multiplies matrices where the search solved linear systems,
`check_cover` verifies closure where the search saturated, and `check_ore`
expands operator products where the search solved a nullspace. One does not,
and says so: `check_projection` reconstructs the witness program with the same
assembler the search used. See forge.closure.projection.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from typing import Sequence

from . import cover as _cover
from . import ore as _ore
from . import projection as _projection
from .kripke import verify as check_kripke  # noqa: F401  (re-exported)
from .words import Model, as_matrix, as_row, dot, mat_mat, rational, vec_mat


def check_observable(model: Model, certificate) -> bool:
    """Verify q = t G, G A_a = C_a G, and G s0 = 0.

    Deliberately NOT checked: that the rows of G are independent, that they
    came from a particular search, or that their number is minimal. Those
    explain the search's efficiency; they are not needed for soundness, and a
    certificate with redundant rows is just as valid.

    The target-membership equation is the one that cannot be dropped. An
    invariant basis without it might certify something irrelevant.
    """
    try:
        if certificate.get('kind') != 'observable-closure':
            return False
        basis = as_matrix(certificate['basis'], cols=model.dimension)
        rank = len(basis)
        target = as_row(certificate['target_coordinates'], rank)
        actions = certificate['actions']
        if not isinstance(actions, list) or len(actions) != len(model.actions):
            return False
        if vec_mat(target, basis) != model.output:
            return False
        if any(dot(row, model.initial) for row in basis):
            return False
        for action, claimed in zip(model.actions, actions):
            coefficients = as_matrix(claimed, rank, rank)
            if mat_mat(basis, action) != mat_mat(coefficients, basis):
                return False
        return True
    except (KeyError, TypeError, ValueError, IndexError, AttributeError):
        return False


def check_separating_word(model: Model, word, value) -> bool:
    """Replay the word in the ORIGINAL matrices and compare the observation."""
    try:
        claimed = rational(value)
        return claimed != 0 and model.evaluate(word) == claimed
    except (KeyError, TypeError, ValueError, IndexError, AttributeError):
        return False


def check_cover(problem, certificate) -> bool:
    """Verify an inductive cover, or evaluate a counterexample tree.

    Never runs reachability. For a cover it checks membership, distinctness,
    every constructor closure, and inclusion in the good set. For a
    counterexample it re-evaluates the node list in the input algebra, with
    every child index strictly below its parent's -- a malformed self-reference
    is rejected even when its claimed summary state happens to be bad.
    """
    try:
        _cover.validate_problem(problem)
        if (certificate.get('schema') != _cover.SCHEMA or
                certificate.get('problem') != problem):
            return False
        states = problem['states']
        good = set(problem['good'])
        kind = certificate['kind']
        if kind == 'cover':
            raw = certificate['cover']
            if (type(raw) is not list or len(raw) != len(set(raw)) or
                    any(type(x) is not int or not 0 <= x < states for x in raw)):
                return False
            claimed = set(raw)
            if not claimed <= good:
                return False
            for index, c in enumerate(problem['constructors']):
                for args in product(raw, repeat=c['arity']):
                    if _cover.transition(problem, index, args) not in claimed:
                        return False
            return True
        if kind == 'counterexample':
            values: list[int] = []
            for node in certificate['nodes']:
                index = node['constructor']
                if (type(index) is not int or
                        not 0 <= index < len(problem['constructors'])):
                    return False
                children = node['children']
                if (type(children) is not list or
                        any(type(i) is not int or not 0 <= i < len(values)
                            for i in children)):
                    return False
                values.append(_cover.transition(problem, index,
                                                [values[i] for i in children]))
            root = certificate['root']
            return (type(root) is int and 0 <= root < len(values) and
                    values[root] not in good)
        return False
    except (KeyError, TypeError, ValueError, IndexError, AttributeError):
        return False


def check_projection(problem, certificate) -> bool:
    """Verify the Bezout receipts, then compare a reconstructed program.

    The receipt check is a genuine asymmetry: g > 0, g | a, g | m and
    u*a + v*m = g already force g to be the positive gcd, and the checker never
    runs the extended Euclidean algorithm. The reconstruction is not: it calls
    the same assembler the search did, so it catches a modified receipt or
    program and not an arithmetic mistake common to both. That is disclosed
    rather than smoothed over, and the test suite addresses it by a different
    route.
    """
    try:
        if (certificate.get('schema') != _projection.SCHEMA or
                certificate.get('problem') != problem):
            return False
        expected = _projection.assemble(problem, certificate['bezout'])

        def integral(value) -> bool:
            # Python equality treats True as 1 and 1.0 as 1; a program full of
            # booleans or floats must not compare equal to an integer one.
            if isinstance(value, dict):
                return all(type(k) is str and integral(v) for k, v in value.items())
            if isinstance(value, list):
                return all(integral(v) for v in value)
            return type(value) in (int, str)

        return (integral(certificate['program']) and
                expected == certificate['program'])
    except (KeyError, ValueError, TypeError, ZeroDivisionError,
            IndexError, AttributeError):
        return False


def _as_operator(raw) -> list:
    operator = [_ore.trim([rational(c) for c in p]) for p in raw]
    while operator and not operator[-1]:
        operator.pop()
    if not operator:
        raise ValueError('empty operator')
    return operator


def check_ore(problem, certificate) -> bool:
    """Check L = U A = V B by expanding both products under the Ore rule.

    Minimality is not asserted and not checked. A non-minimal common multiple
    is a valid certificate; it simply costs more downstream.
    """
    try:
        a = _as_operator(problem['left'])
        b = _as_operator(problem['right'])
        if certificate.get('kind') != 'ore-multiple':
            return False
        common = _as_operator(certificate['common'])
        u = _as_operator(certificate['left_multiplier'])
        v = _as_operator(certificate['right_multiplier'])
        return _ore.ore_mul(u, a) == common == _ore.ore_mul(v, b)
    except (KeyError, TypeError, ValueError, IndexError, AttributeError):
        return False


def check_singularity_plan(problem, certificate) -> bool:
    """Recompute the bound, the roots and the seed set. Trust no supplied list.

    This checks WHICH values must be proved equal. It does not prove those
    equalities, and it establishes nothing about any particular sequence.
    """
    try:
        operator = _as_operator(problem['operator'])
        order = len(operator)-1
        if order < 1:
            return False
        leading = operator[-1]
        degree = len(leading)-1
        if certificate.get('kind') != 'singularity-cover':
            return False
        bound = certificate['bound']
        if type(bound) is not int or not 0 <= bound <= _ore.MAX_BOUND:
            return False
        if degree == 0:
            if bound != 0:
                return False
        else:
            top = leading[degree]
            required = 1 + max(abs(leading[i]/top) for i in range(degree))
            if bound < required:
                return False
        roots = [i for i in range(bound+1) if _ore.peval(leading, i) == 0]
        seeds = sorted(set(range(order)) | {i+order for i in roots})
        for key in ('singular_indices', 'seed_indices'):
            if type(certificate[key]) is not list:
                return False
            if any(type(x) is not int or x < 0 for x in certificate[key]):
                return False
        return (certificate['singular_indices'] == roots and
                certificate['seed_indices'] == seeds)
    except (KeyError, TypeError, ValueError, IndexError, AttributeError):
        return False
