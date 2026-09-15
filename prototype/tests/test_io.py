"""Decoding, replay and Lean emission. Ported from p1, p3, p9, p6 and p5.

The decode half must stay standard-library-only: this suite asserts that nothing
on the replay path imports NumPy, SciPy or SymPy.
"""
import copy
import json
import subprocess
import sys
from fractions import Fraction as Q
from pathlib import Path
import pytest
from forge.poly import Poly
from forge.certificates import check_cone
from forge.cone import discover
from forge.quadratic import quadratic_sos
from forge.recurrence import additive_invariant, synthesize_accumulator
from forge.bernstein import bernstein_search
from forge.io import decode, lean

ROOT = Path(__file__).resolve().parents[1]
BUNDLE = ROOT / 'results' / 'certificates.json'


# --------------------------------------------------------------------------
# p1 + p3: bounded decoders and duplicate-key rejection.
# --------------------------------------------------------------------------
def test_duplicate_json_keys_are_rejected():
    """p3: last-one-wins is a silent semantic change; reject instead."""
    assert decode.loads('{"a": 1, "b": 2}') == {'a': 1, 'b': 2}
    with pytest.raises(decode.DecodeError):
        decode.loads('{"a": 1, "a": 2}')
    with pytest.raises(decode.DecodeError):
        decode.loads('[{"n": 1, "n": 2}]')


@pytest.mark.parametrize('bad', ['1.5', '1e3', ' 1', '1/0', '--1', '1/-2', '', 'x'])
def test_rational_decoder_is_bounded(bad):
    """p1: only a strict decimal integer / fraction spelling is a rational."""
    with pytest.raises(decode.DecodeError):
        decode.rational(bad)
    with pytest.raises(decode.DecodeError):
        decode.rational(1)
    assert decode.rational('-3/4') == Q(-3, 4)
    with pytest.raises(decode.DecodeError):
        decode.rational(str(2 ** 5000))


@pytest.mark.parametrize('bad', [
    {'n': 0, 'terms': []},
    {'n': 99, 'terms': []},
    {'n': 1, 'terms': [[[1], '1'], [[1], '2']]},
    {'n': 1, 'terms': [[[-1], '1']]},
    {'n': 1, 'terms': [[[300], '1']]},
    {'n': 1, 'terms': [['x', '1']]},
    {'n': 1, 'terms': [[[1], 1]]},
    {'n': 1},
])
def test_polynomial_decoder_rejects_bad_shapes(bad):
    """p9's parametrized bad-input matrix, applied at the decode boundary."""
    with pytest.raises(decode.DecodeError):
        decode.polynomial(bad)


def test_polynomial_decoder_round_trip():
    p = Poly.make(2, {(1, 0): Q(3, 4), (0, 2): Q(-1)})
    assert decode.polynomial(p.json()) == p


@pytest.mark.parametrize('bad', [
    [], [['0', '1'], ['1', '0']], [['1', '1']], [['0']], 'box',
])
def test_box_decoder_rejects_degenerate_intervals(bad):
    with pytest.raises(decode.DecodeError):
        decode.box(bad)
    assert decode.box([['0', '1']]) == ((Q(0), Q(1)),)


def test_term_decoder_applies_the_well_typed_gate():
    """p9: a decoded first-order term must be well sorted before use."""
    from forge.terms import F, NIL
    t = F('rev', NIL)
    assert decode.term(t.json()) == t
    with pytest.raises(ValueError):
        decode.term({'symbol': 'rev', 'sort': 'Elem', 'args': [NIL.json()]})
    with pytest.raises(ValueError):
        decode.term({'symbol': 'bogus', 'sort': 'List', 'args': []})


def test_cone_decoder_rejects_malformed_certificates():
    with pytest.raises(decode.DecodeError):
        decode.cone({'terms': []})
    with pytest.raises(decode.DecodeError):
        decode.cone({'terms': [{'weight': '1'}], 'equality_multipliers': []})
    with pytest.raises(decode.DecodeError):
        decode.cone({'terms': [{'weight': '1', 'square': Poly.var(1, 0).json(),
                                'powers': [-1]}], 'equality_multipliers': []})


# --------------------------------------------------------------------------
# The persisted bundle.
# --------------------------------------------------------------------------
@pytest.mark.skipif(not BUNDLE.exists(), reason='run bin/generate.py first')
def test_stored_bundle_replays_and_is_not_vacuous():
    """p6: replay everything, then prove the run was not vacuous."""
    records = decode.loads(BUNDLE.read_text(encoding='utf-8'))
    summary = decode.verify_bundle(records)
    assert summary['records'] == len(records)
    assert summary['mutations_rejected'] > 0
    for family in decode.REQUIRED_FAMILIES:
        assert summary['families'].get(family)


@pytest.mark.skipif(not BUNDLE.exists(), reason='run bin/generate.py first')
def test_missing_required_family_is_a_hard_failure():
    """p6: an empty or mistyped bundle must FAIL, never succeed vacuously."""
    records = decode.loads(BUNDLE.read_text(encoding='utf-8'))
    thinned = [r for r in records if r['family'] != 'Quadratic SOS']
    with pytest.raises(decode.DecodeError):
        decode.verify_bundle(thinned)
    with pytest.raises(decode.DecodeError):
        decode.verify_bundle([])


@pytest.mark.skipif(not BUNDLE.exists(), reason='run bin/generate.py first')
def test_every_record_has_a_rejected_mutation():
    """Each stored family carries at least one mutation that must be rejected."""
    records = decode.loads(BUNDLE.read_text(encoding='utf-8'))
    for record in records:
        muts = decode.mutations(record)
        assert muts, 'no mutation defined for family ' + record['family']
        for bad in muts:
            try:
                accepted = decode.verify(bad)
            except (ValueError, TypeError, KeyError, IndexError):
                accepted = False
            assert not accepted


def test_unknown_family_is_an_error():
    with pytest.raises(decode.DecodeError):
        decode.verify({'family': 'Astrology', 'input': {}, 'certificate': {}})
    with pytest.raises(decode.DecodeError):
        decode.verify({'family': 'Quadratic SOS'})


@pytest.mark.skipif(not BUNDLE.exists(), reason='run bin/generate.py first')
def test_replay_cli_runs_without_site_packages():
    """Requirement: `python -S bin/verify.py` works with no third-party imports."""
    out = subprocess.run([sys.executable, '-S', str(ROOT / 'bin' / 'verify.py')],
                         cwd=str(ROOT), capture_output=True, text=True)
    assert out.returncode == 0, out.stderr
    assert 'certificates rechecked successfully' in out.stdout
    assert 'site packages disabled' in out.stdout


def test_decode_module_pulls_in_no_numeric_library():
    """The whole replay import graph must be standard-library-only."""
    code = ('import sys, forge.io.decode;'
            'print([m for m in ("numpy","scipy","sympy") if m in sys.modules])')
    out = subprocess.run([sys.executable, '-S', '-c', code], cwd=str(ROOT),
                         capture_output=True, text=True)
    assert out.returncode == 0, out.stderr
    assert out.stdout.strip() == '[]'


# --------------------------------------------------------------------------
# p5 + p1 + p7 + p3: Lean emission.
# --------------------------------------------------------------------------
def test_cone_theorem_emission():
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    p = 3 * (x - 2 * y + 1) ** 2 + Q(1, 7) * (x + y) ** 2
    text = lean.cone_theorem('demo', p, (), (), quadratic_sos(p), ['x', 'y'])
    assert 'theorem demo (x y : ℝ)' in text
    assert 'sq_nonneg' in text and 'by ring' in text
    assert 'sorry' not in text


def test_equality_ideal_emission():
    """p5: the ideal part is rewritten away by the he_i hypotheses."""
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    target = x * x + y * y - Q(1, 2)
    es = (x + y - 1,)
    r = discover(target, (), es, degree=2)
    text = lean.cone_theorem('ideal_demo', target, (), es, r.certificate, ['x', 'y'])
    assert '(he0 :' in text and 'rw [hid, hi, add_zero]' in text


def test_invalid_certificate_raises_rather_than_asserts():
    """p3: a raise survives `python -O`; an assert does not."""
    from forge.certificates import ConeCertificate, ConeTerm
    x = Poly.var(1, 0)
    bogus = ConeCertificate((ConeTerm(Q(1), x, ()),))
    with pytest.raises(ValueError):
        lean.cone_theorem('bad', x, (), (), bogus, ['x'])
    with pytest.raises(ValueError):
        lean.bernstein_theorem('bad', x, ((Q(0), Q(1)),),
                               __import__('forge.certificates', fromlist=['x'])
                               .BernsteinLeaf(Q(1)), ['x'])


def test_bernstein_branch_emitter():
    """p1: one Lean case per box, each closed by positivity and ring."""
    x = Poly.var(1, 0)
    p = (x - Q(1, 4)) ** 2 + Q(1, 50)
    box = ((Q(0), Q(1)),)
    tree = bernstein_search(p, box, max_depth=8)
    text = lean.bernstein_theorem('box_demo', p, box, tree, ['x'])
    assert text.count('rcases le_total') >= 1
    assert text.count('by positivity') >= 2
    assert 'by ring' in text


def test_orbit_and_generalizing_emitters():
    """p5's orbit scaffolding and p7's `induction n generalizing a`."""
    u = Poly.var(1, 0)
    text = lean.ORBIT_PREAMBLE + lean.invariant_theorem('cubic', additive_invariant((u + 1) ** 3))
    assert 'orbit_invariant' in text and 'preserved_cubic' in text
    acc, _ = synthesize_accumulator(Poly.var(2, 0) ** 2)
    text = lean.accumulator_theorem('square', Poly.var(2, 0) ** 2, acc)
    assert 'induction n generalizing a' in text


def test_rational_rendering():
    assert lean.rat(Q(3)) == '(3 : ℝ)'
    assert lean.rat(Q(1, 2)) == '((1 : ℝ) / 2)'
    assert lean.number(Q(-1, 3)) == '(-1 / 3)'
    assert lean.poly_lean(Poly.const(1, 0), ['x']) == '(0 : ℝ)'
    with pytest.raises(ValueError):
        lean.poly_lean(Poly.var(2, 0), ['x'])
