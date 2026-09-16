from fractions import Fraction as Q
from pathlib import Path
import pytest
from atlas import exact as E
from atlas.io import load
from atlas.checker import verify,evaluate_formula,selector
from atlas.producer import symbolic
ROOT=Path(__file__).resolve().parents[2]

@pytest.mark.parametrize('wire',[0,1.0,True,'1/1','01','0.0','2/2','-0'])
def test_canonical_rationals(wire):
    with pytest.raises((ValueError,ZeroDivisionError)):E.parse_q(wire)

@pytest.mark.parametrize('p',[(Q(0),Q(1)),(Q(-1),Q(0),Q(1)),(Q(4),Q(0),Q(-4),Q(0),Q(1))])
def test_root_coverage(p):
    rs=E.isolate_roots(p);assert E.verify_root_cover(p,[r.descriptor() for r in rs])
    with pytest.raises(ValueError):E.verify_root_cover(p,[r.descriptor() for r in rs][1:])

def test_endpoint_convention():
    chain=E.sturm((Q(0),Q(1)))
    with pytest.raises(ValueError):E.root_count(chain,Q(0),Q(1))
    assert E.Root((Q(0),Q(1)),Q(0),Q(0)).sign_at((Q(0),Q(1)))==0

def test_localization_not_whole_quotient():
    p=E.mul((Q(-2),Q(0),Q(1)),(Q(-3),Q(0),Q(1)))
    f=E.AField(E.isolate_roots(p)[2])
    assert f.element((Q(1),),(Q(-3),Q(0),Q(1)))==Q(-1)
    with pytest.raises(ZeroDivisionError):f.element((Q(1),),(Q(-2),Q(0),Q(1)))

def test_zero_polynomial_sympy():
    assert symbolic({}).subs('x',1)==0

def test_budget_is_unknown(monkeypatch):
    monkeypatch.setattr(E,'MAX_ISOLATION_NODES',0)
    with pytest.raises(E.LimitExceeded):E.isolate_roots((Q(-2),Q(0),Q(1)))

def test_formula_no_short_circuit_validation():
    with pytest.raises(ValueError):evaluate_formula(['implies',False,['bad']],[])

def test_duplicate_json_key(tmp_path):
    p=tmp_path/'bad.json';p.write_text('{"a":1,"a":2}')
    with pytest.raises(ValueError):load(p)

@pytest.mark.parametrize('directory',sorted((ROOT/'examples').iterdir()),ids=lambda p:p.name)
def test_replay(directory):
    r=verify(load(directory/'problem.json'),load(directory/'certificate.json'))
    assert r['accepted']

def test_strategies_use_roots_not_samples():
    c=load(ROOT/'examples'/'algebraic_positive'/'certificate.json')
    assert selector(c['stacks'][0])['kind']=='root'
