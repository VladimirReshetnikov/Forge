"""Independent SymPy oracles for rational fibers and real-algebraic arithmetic."""
from pathlib import Path
from fractions import Fraction as Q
import json,random,time,sys,platform
import sympy as sp
from atlas import exact as E, polynomial as P
from atlas.producer import x,y,symbolic
from atlas.checker import verify
from atlas.io import load
ROOT=Path(__file__).resolve().parents[1]
SEED=20260915
rng=random.Random(SEED)


def expr_formula(f,polys):
    if type(f) is bool:return sp.true if f else sp.false
    op=f[0]
    rel={'eq':sp.Eq,'ne':sp.Ne,'lt':sp.Lt,'le':sp.Le,'gt':sp.Gt,'ge':sp.Ge}
    if op in rel:return rel[op](polys[f[1]],0)
    if op=='not':return sp.Not(expr_formula(f[1],polys))
    if op=='implies':return sp.Implies(expr_formula(f[1],polys),expr_formula(f[2],polys))
    return (sp.And if op=='and' else sp.Or)(*[expr_formula(v,polys) for v in f[1:]])


def exists_univariate(formula):
    dnf=sp.to_dnf(formula,simplify=True,force=True)
    if dnf is sp.true:return True
    if dnf is sp.false:return False
    clauses=dnf.args if isinstance(dnf,sp.Or) else (dnf,)
    for c in clauses:
        atoms=c.args if isinstance(c,sp.And) else (c,)
        answer=sp.reduce_inequalities(list(atoms),y)
        if answer is not sp.false:return True
    return False


def cell_for_q(c,q):
    p=P.decode_dense(c['projection'])
    roots=E.verify_root_cover(p,c['base_roots'])
    for i,r in enumerate(roots):
        s=r.sign_at((-q,Q(1)))
        if s==0:return 2*i+1
        if s>0:return 2*i
    return 2*len(roots)


def main():
    results={};t=time.perf_counter()
    root_records=[]
    for k in range(250):
        degree=rng.randint(1,6)
        coeff=[Q(rng.randint(-5,5)) for _ in range(degree)]+[Q(rng.choice([-3,-2,-1,1,2,3]))]
        p=E.trim(coeff); sf=E.squarefree(p);rs=E.isolate_roots(sf)
        symbolic_p=sp.Poly(sum(sp.Rational(a.numerator,a.denominator)*y**i for i,a in enumerate(sf)),y)
        expected=int(symbolic_p.count_roots(-sp.oo,sp.oo))
        assert len(rs)==expected
        for r in rs:
            if r.lo==r.hi:assert symbolic_p.eval(sp.Rational(r.lo.numerator,r.lo.denominator))==0
            else:assert symbolic_p.count_roots(sp.Rational(r.lo.numerator,r.lo.denominator),sp.Rational(r.hi.numerator,r.hi.denominator))==1
        root_records.append({'coefficients':P.encode_dense(p),'roots':len(rs)})
    results['rational_root_cases']={'cases':len(root_records),'agreements':len(root_records),'records':root_records}
    # Reducible defining polynomial: sqrt(2) is selected, other roots remain in P.
    base=E.mul((Q(-2),Q(0),Q(1)),(Q(-3),Q(0),Q(1)))
    r=E.isolate_roots(base)[2];field=E.AField(r);alg=[];zero_den=0
    for k in range(200):
        n=E.trim(Q(rng.randint(-3,3)) for _ in range(rng.randint(1,6)))
        d=E.trim(Q(rng.randint(-3,3)) for _ in range(rng.randint(1,5)))
        ns=sum(sp.Rational(a.numerator,a.denominator)*sp.sqrt(2)**i for i,a in enumerate(n))
        ds=sp.simplify(sum(sp.Rational(a.numerator,a.denominator)*sp.sqrt(2)**i for i,a in enumerate(d)))
        if ds==0:
            try:field.element(n,d)
            except ZeroDivisionError:zero_den+=1;continue
            raise AssertionError('accepted zero algebraic denominator')
        expected=sp.sign(sp.simplify(ns/ds))
        assert expected in (-1,0,1),expected
        actual=field.element(n,d).sign();assert actual==expected
        alg.append({'num':P.encode_dense(n),'den':P.encode_dense(d),'sign':actual})
    results['localized_algebraic_cases']={'attempts':200,'agreements':len(alg),'zero_denominators_rejected':zero_den,'records':alg}
    # A denominator that is a zero divisor modulo P but nonzero at sqrt(2).
    a=field.element((Q(1),),(Q(-3),Q(0),Q(1)))
    assert a.sign()==-1 and a==Q(-1)
    results['nonfield_quotient_control']=True
    # Off-sample x values; SymPy independently solves the complete y-fiber.
    probes=[Q(-5),Q(-3),Q(-2),Q(-1),Q(-1,2),Q(-1,4),Q(0),Q(1,4),Q(1,2),Q(1),Q(3,2),Q(2),Q(3),Q(5)]
    fiber=[];unknown=[]
    for path in sorted((ROOT/'examples').glob('*/problem.json')):
        p,c=load(path),load(path.with_name('certificate.json'))
        polys=[symbolic(P.decode(v)) for v in p['polynomials']]
        for q in probes:
            f=expr_formula(p['formula'],[sp.expand(v.subs(x,sp.Rational(q.numerator,q.denominator))) for v in polys])
            try:
                expected=exists_univariate(f) if p['inner']=='exists' else not exists_univariate(sp.Not(f))
            except (NotImplementedError,ValueError) as ex:
                unknown.append({'name':p['name'],'x':str(q),'reason':str(ex)});continue
            actual=c['truth_by_x'][cell_for_q(c,q)]
            assert actual==expected,(p['name'],q,actual,expected,f)
            fiber.append({'name':p['name'],'x':str(q),'value':actual})
    results['rational_fiber_oracle']={'attempts':len(fiber)+len(unknown),'agreements':len(fiber),'unknown':unknown,'records':fiber}
    # Independently check exact free-parameter answers at every base cell.
    region={
      'two_shifted_squares':lambda z:sp.Or(sp.Eq(z,0),sp.Eq(z*z,8)),
      'overlapping_intervals':lambda z:sp.Ge(z,1),
      'uniform_positive_quadratic':lambda z:sp.Lt(z*z,4),
      'degree_drop_at_zero':lambda z:sp.Ge(4*z+1,0),
      'strict_and_disequality':lambda z:sp.Gt(z,0),
    }
    exact_regions=[]
    for name,f in region.items():
        c=load(ROOT/'examples'/name/'certificate.json')
        proj=P.decode_dense(c['projection'])
        expr=sum(sp.Rational(a.numerator,a.denominator)*x**i for i,a in enumerate(proj))
        roots=sp.real_roots(expr,x)
        for i,stack in enumerate(c['stacks']):
            z=roots[i//2] if i%2 else sp.Rational(stack['sample'])
            truth=sp.simplify(f(z))
            assert truth in (sp.true,sp.false),(name,z,truth)
            assert bool(truth)==stack['value']
            exact_regions.append({'name':name,'base_cell':i,'expected':bool(truth)})
    results['exact_free_parameter_regions']={'regions':len(region),'base_cells':len(exact_regions),'agreements':len(exact_regions),'records':exact_regions}
    results['environment']={'python':sys.version,'sympy':sp.__version__,'platform':platform.platform(),'seed':SEED,'seconds':time.perf_counter()-t}
    (ROOT/'results'/'differential.json').write_text(json.dumps(results,indent=2)+'\n')
    print({k:{a:b for a,b in v.items() if a!='records'} if isinstance(v,dict) else v for k,v in results.items()})

if __name__=='__main__':main()
