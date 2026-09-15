"""Box subdivision. Ported from p8's, p3's and p2's positivity suites."""
from dataclasses import replace
from fractions import Fraction as Q
import random
import pytest
from forge.poly import Poly, bernstein_coefficients
from forge import bernstein


@pytest.mark.parametrize('k,epsilon', [(k, Q(1, d)) for k in range(1, 7)
                                       for d in (10, 100, 1000)])
def test_bernstein_positive(k, epsilon):
    """p8: strict positivity on a box, proved and independently replayed."""
    x = Poly.var(1, 0)
    p = (x - Q(k, 7)) ** 2 + epsilon
    box = ((Q(0), Q(1)),)
    r = bernstein.search(p, box, strict=True)
    assert r.status == 'PROVED'
    assert bernstein.replay(p, box, r.tree, strict=True)


def test_bernstein_refute_unknown_and_mutations():
    """p8: PROVED / REFUTED(witness) / UNKNOWN stay three distinct answers."""
    x = Poly.var(1, 0)
    box = ((Q(0), Q(1)),)
    r = bernstein.search((x - Q(1, 3)) ** 2 + Q(1, 100), box)
    assert isinstance(r.tree, bernstein.Split)
    assert not bernstein.replay((x - Q(1, 3)) ** 2 + 1, box, r.tree)
    assert not bernstein.replay((x - Q(1, 3)) ** 2 + Q(1, 100), box, replace(r.tree, cut=Q(0)))
    assert not bernstein.replay((x - Q(1, 3)) ** 2 + Q(1, 100), box, replace(r.tree, right=None))
    assert not bernstein.replay(x, box, bernstein.Leaf((Q(1), Q(1))))
    assert not bernstein.replay(x, box, bernstein.Leaf((Q(0), Q(1))), strict=True)
    assert bernstein.replay(x, box, bernstein.Leaf((Q(0), Q(1))))
    bad = bernstein.search(x - Q(1, 2), box)
    assert bad.status == 'REFUTED' and bernstein.check_witness(x - Q(1, 2), box, bad.witness)
    assert not bernstein.check_witness(x, box, (Q(-1),))
    unresolved = bernstein.search((x * x - 2) ** 2, ((Q(1), Q(2)),), max_depth=8)
    assert unresolved.status == 'UNKNOWN' and unresolved.witness is None
    assert bernstein.search(x, box, strict=True).status == 'REFUTED'


@pytest.mark.parametrize('seed', range(15))
def test_bernstein_conversion_independent_expansion(seed):
    """p8: randomized round-trip through a DIFFERENT algorithm than the producer."""
    rng = random.Random(seed)
    p = Poly.make(2, {(i, j): Q(rng.randint(-5, 5)) for i in range(3) for j in range(3)})
    box = ((Q(-2), Q(3)), (Q(1), Q(4)))
    _, cs = bernstein_coefficients(p, box)
    shift = -min(cs) + 1
    assert bernstein.replay(p + shift, box, bernstein.Leaf(tuple(c + shift for c in cs)))
    assert not bernstein.replay(p + shift + 1, box,
                                bernstein.Leaf(tuple(c + shift for c in cs)))


def test_subdivision_adds_a_certificate():
    """p2: depth 0 abstains where depth 1 succeeds."""
    x = Poly.var(1, 0)
    p = (x - Q(1, 2)) ** 2 + Q(1, 100)
    box = ((Q(0), Q(1)),)
    assert bernstein.search(p, box, max_depth=0, strict=True).status == 'UNKNOWN'
    full = bernstein.search(p, box, max_depth=1, strict=True)
    assert full.status == 'PROVED' and bernstein.size(full.tree)[1] == 2


def test_strict_and_weak_signs_distinguished():
    """p2: >= 0 and > 0 are different questions with different answers."""
    x = Poly.var(1, 0)
    box = ((Q(0), Q(1)),)
    assert bernstein.search(x ** 2, box).status == 'PROVED'
    assert bernstein.search(x ** 2, box, strict=True).status == 'REFUTED'


def test_refutation_is_a_checked_point():
    x = Poly.var(1, 0)
    p = x ** 2 - Q(1, 2)
    r = bernstein.search(p, ((Q(-1), Q(1)),))
    assert r.status == 'REFUTED' and p.evaluate(r.witness) < 0


@pytest.mark.parametrize('mode', ['relative', 'width', 'depth'])
def test_axis_selection_modes_all_certify(mode):
    """p3's relative-width and p2's fair-shrink selection are both available."""
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    p = (x - Q(1, 3)) ** 2 + (y - Q(1, 5)) ** 2 + Q(1, 50)
    box = ((Q(0), Q(1)), (Q(0), Q(4)))
    r = bernstein.search(p, box, max_depth=10, axis_mode=mode)
    assert r.status == 'PROVED'
    assert bernstein.replay(p, box, r.tree)
    with pytest.raises(ValueError):
        bernstein.search(p, box, axis_mode='nonsense')


def test_diagonal_square_budget_unknown_not_false():
    """p2: exhausting the budget is UNKNOWN with no counterexample."""
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    r = bernstein.search((x - y) ** 2, ((Q(0), Q(1)), (Q(0), Q(1))),
                         max_depth=4, strict=True)
    assert r.status in ('UNKNOWN', 'REFUTED')
    if r.status == 'UNKNOWN':
        assert r.witness is None


def test_leaf_degrees_come_from_the_transformed_polynomial():
    """Correctness fix: replay derives degrees from p after the affine map."""
    x = Poly.var(1, 0)
    p = x ** 2 + 100
    box = ((Q(-3), Q(5)),)
    transformed = p.affine_box(box)
    _, cs = bernstein_coefficients(p, box)
    assert len(cs) == transformed.degrees[0] + 1 == 3
    assert min(cs) >= 0
    assert bernstein.replay(p, box, bernstein.Leaf(cs))
    assert not bernstein.replay(p, box, bernstein.Leaf(cs[:-1]))
    assert not bernstein.replay(p, box, bernstein.Leaf(cs + (Q(1),)))


def test_search_validates_its_domain():
    x = Poly.var(1, 0)
    with pytest.raises(ValueError):
        bernstein.search(x, ((Q(1), Q(0)),))
    with pytest.raises(ValueError):
        bernstein.search(x, ((Q(0), Q(1)),), max_nodes=0)
    with pytest.raises(ValueError):
        bernstein.bernstein_search(x, ((Q(0), Q(1)),), max_depth=-1)
