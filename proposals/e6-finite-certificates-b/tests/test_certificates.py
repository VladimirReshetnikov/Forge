"""Independent replay, semantic mutations, and differential controls."""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
import json
from math import comb
from pathlib import Path
import random
import pytest
import sympy as s
from prototype import check as c
from prototype.encode import polynomial
from prototype.ideal import TrackedGB, Limits, BudgetExceeded, discover as ideals
from prototype.weighted import discover as weighted
from prototype.telescoping import discover as telescope, n, k

ROOT = Path(__file__).resolve().parents[1]
CORPUS = c.load(ROOT/'results/certificates.json')
BYID = {row['id']:row for row in CORPUS}
IDEALS = [row for row in CORPUS if row['certificate']['kind']=='inductive_ideal_v1']
CLOSURES = [row for row in CORPUS if row['certificate']['kind']=='weighted_closure_v1' and row['certificate']['rank']]
WORDS = [row for row in CORPUS if row['certificate']['kind']=='distinguishing_word_v1']
TELESCOPERS = [row for row in CORPUS if row['certificate']['kind']=='binomial_telescoper_v1']

def encode_dict(p):
    return [[list(e),[v.numerator,v.denominator]] for e,v in sorted(p.items()) if v]

def plus_one(p, dim):
    return encode_dict(c.add(c.poly(p,dim),c.const(1,dim)))

@pytest.mark.parametrize('row',CORPUS,ids=lambda row:row['id'])
def test_stored_replay(row):
    assert isinstance(c.verify(row['problem'],row['certificate']),dict)

@pytest.mark.parametrize('row',IDEALS,ids=lambda row:row['id'])
def test_ideal_target_substitution_rejected(row):
    p=deepcopy(row['problem']);p['goal']=plus_one(p['goal'],p['dimension'])
    with pytest.raises(c.Rejected,match='goal ideal identity'):
        c.verify(p,row['certificate'])

@pytest.mark.parametrize('row',IDEALS,ids=lambda row:row['id'])
def test_ideal_step_mutation_rejected(row):
    p=row['problem']; cert=deepcopy(row['certificate'])
    cert['steps'][0][0][0]=plus_one(cert['steps'][0][0][0],p['dimension'])
    with pytest.raises(c.Rejected,match='transition identity'):
        c.verify(p,cert)

@pytest.mark.parametrize('row',CLOSURES,ids=lambda row:row['id'])
def test_weighted_span_mutation_rejected(row):
    cert=deepcopy(row['certificate'])
    q=c.rat(cert['initial_coordinates'][0])+1
    cert['initial_coordinates'][0]=[q.numerator,q.denominator]
    with pytest.raises(c.Rejected,match='initial span'):
        c.verify(row['problem'],cert)

@pytest.mark.parametrize('row',[row for row in CLOSURES if row['problem']['alphabet']],ids=lambda row:row['id'])
def test_weighted_closure_mutation_rejected(row):
    cert=deepcopy(row['certificate']); a=row['problem']['alphabet'][0]
    q=c.rat(cert['closure'][a][0][0])+1
    cert['closure'][a][0][0]=[q.numerator,q.denominator]
    with pytest.raises(c.Rejected,match='closure identity'):
        c.verify(row['problem'],cert)

@pytest.mark.parametrize('row',WORDS,ids=lambda row:row['id'])
def test_false_counterexample_rejected(row):
    # All generated negative fixtures deliberately agree on the empty word.
    cert={'kind':'distinguishing_word_v1','word':[]}
    with pytest.raises(c.Rejected,match='does not distinguish'):
        c.verify(row['problem'],cert)

@pytest.mark.parametrize('row',TELESCOPERS,ids=lambda row:row['id'])
def test_telescoper_numerator_rejected(row):
    cert=deepcopy(row['certificate']);cert['numerator']=plus_one(cert['numerator'],2)
    with pytest.raises(c.Rejected,match='interior polynomial identity'):
        c.verify(row['problem'],cert)

@pytest.mark.parametrize('row',TELESCOPERS,ids=lambda row:row['id'])
def test_telescoper_initial_rejected(row):
    cert=deepcopy(row['certificate']);cert['initial_values'][0]+=1
    with pytest.raises(c.Rejected,match='initial values'):
        c.verify(row['problem'],cert)

@pytest.mark.parametrize('row',TELESCOPERS,ids=lambda row:row['id'])
def test_singular_but_true_recurrence_not_uniqueness_receipt(row):
    cert=deepcopy(row['certificate'])
    fac=c.add(c.var(0,1),c.const(-2,1))
    cert['coefficients']=[encode_dict(c.mul(c.poly(p,1),fac)) for p in cert['coefficients']]
    fac2=c.add(c.var(0,2),c.const(-2,2))
    cert['numerator']=encode_dict(c.mul(c.poly(cert['numerator'],2),fac2))
    # Every identity still holds. Only the leading nonvanishing condition fails.
    with pytest.raises(c.Rejected,match='leading coefficient positivity'):
        c.verify(row['problem'],cert)

@pytest.mark.parametrize('raw',['{"x":1,"x":2}','[0.5]','[NaN]','[Infinity]'])
def test_json_rejections(raw,tmp_path):
    p=tmp_path/'bad.json';p.write_text(raw)
    with pytest.raises(c.Rejected):c.load(p)

@pytest.mark.parametrize('bad',[[1,0],[True,1],[1.0,1],[2,2],[1,-1]])
def test_bad_rationals(bad):
    with pytest.raises(c.Rejected):c.rat(bad)

@pytest.mark.parametrize('bad',[
    [[[0],[0,1]]],[[[0],[1,1]],[[0],[1,1]]],
    [[[1],[1,1]],[[0],[1,1]]],[[[-1],[1,1]]],[[[0,0],[1,1]]]])
def test_bad_polynomials(bad):
    with pytest.raises(c.Rejected):c.poly(bad,1)

def test_missing_guard_not_silently_erased():
    row=deepcopy(BYID['ideal_guarded_update']);row['problem']['transitions'][0]['guards']=[]
    with pytest.raises(c.Rejected):c.verify(row['problem'],row['certificate'])

def test_missing_letter_not_silently_erased():
    row=deepcopy(BYID['weighted_subsequence_product']);del row['certificate']['closure']['b']
    with pytest.raises(c.Rejected,match='missing closure'):c.verify(row['problem'],row['certificate'])

def test_false_source_family_rejected():
    row=deepcopy(TELESCOPERS[0]);row['problem']['family']='arbitrary_expression'
    with pytest.raises(c.Rejected,match='unsupported'):c.verify(row['problem'],row['certificate'])

@pytest.mark.parametrize('seed',range(24))
def test_tracked_groebner_against_sympy(seed):
    rng=random.Random(seed);x,y=s.symbols('x y')
    gens=[x*x+rng.randint(-2,2)*y+rng.randint(-2,2),
          x*y+rng.randint(-2,2)*x+rng.randint(-2,2)*y+rng.randint(-2,2)]
    gb=TrackedGB(gens,(x,y)); oracle=s.groebner(gens,x,y,order='lex',domain=s.QQ)
    # Reduced normal forms can differ for a non-reduced basis; their difference
    # must be in the ideal, and zero membership must agree.
    f=x**3+rng.randint(-3,3)*x*y*y+rng.randint(-3,3)*y+1
    nf=gb.normal(f);onf=oracle.reduce(f)[1]
    assert oracle.reduce(nf-onf)[1]==0
    assert (nf==0)==(onf==0)
    h=s.expand((x-y)*gens[0]+(x+y*y)*gens[1])
    lift=gb.lift(h);assert lift is not None
    ch=c.poly(polynomial(h,(x,y)),2)
    rhs=c.lincomb([c.poly(polynomial(p,(x,y)),2) for p in lift],
                  [c.poly(polynomial(p,(x,y)),2) for p in gens])
    assert ch==rhs
    for g,rep in zip(gb.g,gb.reps):
        assert s.expand(g-sum(a*b for a,b in zip(rep,gens)))==0

@pytest.mark.parametrize('seed',range(60))
def test_weighted_exhaustive_small_oracle(seed):
    rng=random.Random(1000+seed);d=1+seed%4
    a=s.Matrix([[rng.randint(-1,1) for _ in range(d)]])
    b=s.Matrix([rng.randint(-1,1) for _ in range(d)])
    ms={z:s.Matrix(d,d,lambda i,j:rng.randint(-1,1)) for z in ['a','b']}
    pair,info=weighted(a,ms,b); assert pair is not None
    c.verify(*pair)
    witness=None
    for length in range(d):
        for word in product(ms,repeat=length):
            v=a
            for z in word:v=v*ms[z]
            if (v*b)[0]!=0:witness=word;break
        if witness is not None:break
    cert=pair[1]
    assert (witness is None)==(cert['kind']=='weighted_closure_v1')
    if witness is not None: assert len(cert['word'])==len(witness)

@pytest.mark.parametrize('row',TELESCOPERS,ids=lambda row:row['id'])
def test_recurrence_by_finite_sums_extra_regression(row):
    m=row['problem']['power'];r=row['certificate']['order']
    ps=[c.poly(p,1) for p in row['certificate']['coefficients']]
    for nn in range(31):
        total=Q(0)
        for j,p in enumerate(ps):
            v=sum(co*nn**e[0] for e,co in p.items())
            total+=v*sum(comb(nn+j,kk)**m for kk in range(nn+j+1))
        assert total==0

@pytest.mark.parametrize('args',[(2,1,0,0),(3,1,2,2)])
def test_bounded_telescoping_miss(args):
    result,info=telescope(*args);assert result is None

def test_ideal_degree_failure_and_success():
    x=s.symbols('x')
    no,info=ideals((x,),[((),[s.Integer(0)])],[([1-x],[])],x*x-x,degree=1)
    assert no is None
    yes,info=ideals((x,),[((),[s.Integer(0)])],[([1-x],[])],x*x-x,degree=2)
    assert info['dimensions']==[2,1,1]
    c.verify(*yes)

def test_resource_cutoffs_remain_inconclusive():
    x,y=s.symbols('x y')
    with pytest.raises(BudgetExceeded):TrackedGB([x*x-y,x*y-1],(x,y),Limits(max_pairs=0))
    pair,info=weighted(s.Matrix([[1]]),{'a':s.Matrix([[1]])},s.Matrix([0]),max_vectors=0)
    assert pair is None and info['reason']=='vector_budget'

def test_search_checker_import_separation():
    for file in ['ideal.py','weighted.py','telescoping.py','encode.py']:
        text=(ROOT/'prototype'/file).read_text()
        assert 'import check' not in text and 'from .check' not in text
    import ast
    tree=ast.parse((ROOT/'prototype/check.py').read_text())
    imports=[node for node in ast.walk(tree) if isinstance(node,(ast.Import,ast.ImportFrom))]
    assert all('sympy' not in ast.unparse(node) for node in imports)
