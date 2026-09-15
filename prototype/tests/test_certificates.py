"""The checkers themselves. Ported from p1, p5 and p9 certificate test suites."""
from dataclasses import replace
from fractions import Fraction as Q
import pytest
from forge.poly import Poly
from forge.certificates import (ConeTerm, ConeCertificate, check_cone,
                                InvariantCertificate, check_invariant,
                                BernsteinLeaf, BernsteinSplit, check_bernstein,
                                CoefficientLeaf, check_bernstein_expansion,
                                powers_from_indices, tree_size, cone_json,
                                bernstein_coefficients, split_box)
from forge.bernstein import bernstein_search, discover_coefficient_tree


def test_cone_identity_and_scope():
    """p1: hypotheses are supplied by the caller and can never disappear."""
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    p = x * (1 - x) + y * (1 - y)
    cert = ConeCertificate((ConeTerm(Q(1), Poly.const(2, 1), (1, 1, 0, 0)),
                            ConeTerm(Q(1), Poly.const(2, 1), (0, 0, 1, 1))))
    gs = [x, 1 - x, y, 1 - y]
    assert check_cone(p, gs, [], cert)
    assert not check_cone(p, [], [], cert)
    assert not check_cone(p, [x, 1 + x, y, 1 - y], [], cert)
    assert not check_cone(p, gs, [], replace(cert, terms=cert.terms[:1]))


def test_guard_is_not_an_unconditional_fact():
    """p9: a conditional conclusion is not an unconditional one."""
    x = Poly.var(1, 0)
    cert = ConeCertificate((ConeTerm(Q(1), Poly.const(1, 1), (1,)),))
    assert check_cone(x, (x,), (), cert)
    assert not check_cone(x, (), (), ConeCertificate((ConeTerm(Q(1), Poly.const(1, 1), ()),)))
    assert x.evaluate((-1,)) < 0


def test_float_tolerance_exploit_is_rejected_exactly():
    """p5: a weight off by 1e-20 is a different number, not a rounding detail."""
    x = Poly.var(1, 0)
    one = Poly.const(1, 1)
    c = ConeCertificate((ConeTerm(Q(1), one, (1,)),))
    assert check_cone(x, (x,), (), c)
    exploit = replace(c, terms=(replace(c.terms[0], weight=Q(10 ** 20 + 1, 10 ** 20)),))
    assert not check_cone(x, (x,), (), exploit)
    assert not check_cone(x, (x,), (), replace(c, terms=(replace(c.terms[0], weight=Q(-1)),)))
    assert not check_cone(x + 1, (x,), (), c)
    assert not check_cone(x, (x,), (), replace(c, equality_multipliers=(one,)))


@pytest.mark.parametrize('bad', ['negative', 'wrong_target', 'bad_power',
                                 'wrong_dimension', 'float_weight', 'bool_weight',
                                 'not_a_certificate', 'power_count'])
def test_cone_rejects_mutations(bad):
    """p9's parametrized bad-input matrix, on the merged power-tuple format."""
    x = Poly.var(1, 0)
    p = x * x
    gs = ()
    cert = ConeCertificate((ConeTerm(Q(1), x, ()),))
    if bad == 'negative':
        cert = ConeCertificate((ConeTerm(Q(-1), x, ()),))
    elif bad == 'wrong_target':
        p = p - Q(1, 1000000000000)
    elif bad == 'bad_power':
        gs = (x,)
        cert = ConeCertificate((ConeTerm(Q(1), x, (-1,)),))
    elif bad == 'wrong_dimension':
        cert = ConeCertificate((ConeTerm(Q(1), Poly.var(2, 0), ()),))
    elif bad == 'float_weight':
        cert = ConeCertificate((ConeTerm(1.0, x, ()),))
    elif bad == 'bool_weight':
        cert = ConeCertificate((ConeTerm(True, x, ()),))
    elif bad == 'not_a_certificate':
        cert = 'certificate'
    else:
        gs = (x,)
        cert = ConeCertificate((ConeTerm(Q(1), x, ()),))
    assert not check_cone(p, gs, (), cert)


def test_powers_from_indices():
    assert powers_from_indices((0, 0, 2), 3) == (2, 0, 1)
    with pytest.raises(ValueError):
        powers_from_indices((3,), 2)


def test_cone_json_round_trip_shape():
    x = Poly.var(1, 0)
    cert = ConeCertificate((ConeTerm(Q(3, 2), x, ()),), ())
    d = cone_json(cert)
    assert d['terms'][0]['weight'] == '3/2' and d['equality_multipliers'] == []


@pytest.mark.parametrize('power', range(7))
def test_invariant_certificates(power):
    """p5: conserved-quantity certificates and their mutations."""
    from forge.recurrence import additive_invariant
    x = Poly.var(1, 0)
    c = additive_invariant((x + 1) ** power)
    assert c is not None and check_invariant(c)
    assert not check_invariant(replace(c, invariant=c.invariant + 1))
    ts = list(c.transition)
    ts[1] += 1
    assert not check_invariant(replace(c, transition=tuple(ts)))
    assert not check_invariant(InvariantCertificate(c.invariant, (Q(0), Q(1)), c.transition))


def test_bernstein_cover_and_tampering():
    """p1: every leaf AND complete domain coverage are checked."""
    x = Poly.var(1, 0)
    p = x * x - x + Q(1, 3)
    box = ((Q(0), Q(1)),)
    tree = bernstein_search(p, box, max_depth=6)
    assert tree is not None and check_bernstein(p, box, tree)
    assert tree_size(tree) == (2, 1)
    assert not check_bernstein(p, box, replace(tree, point=Q(1, 3)))
    assert not check_bernstein(p, box, replace(tree, left=BernsteinLeaf(Q(1))))
    assert not check_bernstein(p, box, BernsteinLeaf(Q(1)))
    assert not check_bernstein(p, box, replace(tree, left=None))
    assert not check_bernstein(p - 1, box, tree)
    assert not check_bernstein(p, box, replace(tree, left=BernsteinLeaf(Q(-1))))
    assert not check_bernstein(p, box, tree, max_nodes=1)


def test_split_box_rejects_exterior_points():
    box = ((Q(0), Q(1)),)
    assert split_box(box, 0, Q(1, 2)) == ((((Q(0), Q(1, 2))),), ((Q(1, 2), Q(1)),))
    with pytest.raises(ValueError):
        split_box(box, 0, Q(2))
    with pytest.raises(ValueError):
        split_box(box, 1, Q(1, 2))


def test_bernstein_expansion_in_original_coordinates():
    """p5: reconstruct the identity in x, not in the search's t coordinates."""
    x = Poly.var(1, 0)
    p = x * x - x + Q(1, 3)
    box = ((Q(0), Q(1)),)
    tree = discover_coefficient_tree(p, box, depth=4)
    assert tree is not None and check_bernstein_expansion(p, box, tree)
    assert not check_bernstein_expansion(p, box, replace(tree, cut=Q(1, 3)))
    assert not check_bernstein_expansion(p, box, replace(tree, right=tree.left))
    leaf = tree.left
    cs = list(leaf.coefficients)
    k, c = cs[0]
    cs[0] = (k, c + Q(1, 10 ** 18))
    assert not check_bernstein_expansion(p, leaf.box, replace(leaf, coefficients=tuple(cs)))
    assert not check_bernstein_expansion(p, ((Q(0), Q(2)),), tree)
    assert not check_bernstein_expansion(p, leaf.box, replace(leaf, degrees=(3,)))


def test_bernstein_coefficient_values_are_exact():
    x = Poly.var(1, 0)
    p = x * x - x + Q(3, 10)
    coefficients = bernstein_coefficients(p, ((Q(0), Q(1)),))
    assert coefficients == {(0,): Q(3, 10), (1,): Q(-1, 5), (2,): Q(3, 10)}


def test_tensor_size_cap():
    x = Poly.var(1, 0)
    with pytest.raises(ValueError):
        bernstein_coefficients(x ** 40, ((Q(0), Q(1)),), max_coefficients=8)
