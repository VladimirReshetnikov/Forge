"""Search/replay regressions and deliberately hostile certificate controls."""
import copy
from fractions import Fraction as Q
import itertools,json,random,tempfile,unittest
from pathlib import Path
import sympy as s
from cases import corpus
from search import System,Edge,Limits,solve,substitute,poly_json
from verify_stdlib import (Rejected,BudgetExceeded,check_certificate,check_counterexample,
                          parse_problem,polynomial,rational,read_json,Arithmetic)

ROOT=Path(__file__).resolve().parents[1]/'results'/'experiment'
CASES={c.system.name:c for c in corpus()}

def recorded(name,mode='ideal'):
    return (json.loads((ROOT/'problems'/f'{name}.json').read_text()),
            json.loads((ROOT/'evidence'/f'{name}.{mode}.json').read_text()))

class CheckerControls(unittest.TestCase):
    def setUp(self):self.P,self.C=recorded('scaled_graph_00')
    def reject(self,p=None,c=None):
        with self.assertRaises(Rejected):check_certificate(p or self.P,c or self.C)
    def test_valid_certificate(self):self.assertTrue(check_certificate(self.P,self.C)['accepted'])
    def test_wrong_initial(self):
        self.P['initial'][0]['state'][1]=[[[0],['1','1']]];self.reject()
    def test_wrong_target(self):
        self.P['targets'][0]['polynomial']=[[[0,0],['1','1']]];self.reject()
    def test_wrong_transition(self):
        self.P['edges'][0]['update'][1].insert(0,[[0,0,0],['1','1']]);self.reject()
    def test_missing_transition_matrix(self):self.C['step']=[];self.reject()
    def test_missing_transition_row(self):self.C['step'][0]=[];self.reject()
    def test_missing_transition_column(self):self.C['step'][0][0]=[];self.reject()
    def test_wrong_multiplier(self):self.C['step'][0][0][0][0][1]=['3','1'];self.reject()
    def test_empty_basis(self):self.C['basis']=[[]];self.reject()
    def test_wrong_basis_dimension(self):self.C['basis'][0][0][0][0]=[0];self.reject()
    def test_certificate_selects_target(self):self.C['target_index']=0;self.reject()
    def test_duplicate_monomial(self):
        self.C['basis'][0][0].append(copy.deepcopy(self.C['basis'][0][0][-1]));self.reject()
    def test_unsorted_monomials(self):self.C['basis'][0][0].reverse();self.reject()
    def test_zero_term(self):self.C['basis'][0][0][0][1]=['0','1'];self.reject()
    def test_float_coefficient(self):self.C['basis'][0][0][0][1]=0.5;self.reject()
    def test_boolean_exponent(self):self.C['basis'][0][0][0][0][0]=True;self.reject()
    def test_noncanonical_rational(self):self.C['basis'][0][0][0][1]=['2','2'];self.reject()
    def test_negative_denominator(self):self.C['basis'][0][0][0][1]=['1','-1'];self.reject()
    def test_rational_negative_zero(self):
        with self.assertRaises(Rejected):rational(['-0','1'])
    def test_nonfinite_json(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'bad.json';p.write_text('{"x":NaN}')
            with self.assertRaises(Rejected):read_json(p)
    def test_duplicate_json_key(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'bad.json';p.write_text('{"x":1,"x":2}')
            with self.assertRaises(Rejected):read_json(p)
    def test_checker_budget(self):
        with self.assertRaises(BudgetExceeded):check_certificate(self.P,self.C,operation_limit=0)
    def test_multiple_locations(self):
        p,c=recorded('control_locations_00');self.assertTrue(check_certificate(p,c)['accepted'])
        p['edges'][0]['src']=1
        with self.assertRaises(Rejected):check_certificate(p,c)
    def test_multiple_targets(self):
        p,c=recorded('multiple_targets');self.assertTrue(check_certificate(p,c)['accepted'])
        c['target'].pop()
        with self.assertRaises(Rejected):check_certificate(p,c)
    def test_two_inputs_and_swapping(self):
        for name in ('two_fresh_inputs','simultaneous_swap'):
            p,c=recorded(name);self.assertTrue(check_certificate(p,c)['accepted'])
    def test_vacuous_unreachable_location(self):
        p,c=recorded('unreachable_observation');self.assertTrue(check_certificate(p,c)['accepted'])
        p['initial'][0]['location']=1
        with self.assertRaises(Rejected):check_certificate(p,c)

class WitnessControls(unittest.TestCase):
    def test_mutant_length_two(self):
        p,c=recorded('nonlinear_mutant_00');r=check_counterexample(p,c)
        self.assertEqual(r['length'],2);self.assertEqual(r['value'],['-1','1'])
    def test_delete_last_step(self):
        p,c=recorded('nonlinear_mutant_00');c['steps'].pop()
        with self.assertRaises(Rejected):check_counterexample(p,c)
    def test_bad_control_order(self):
        p,c=recorded('ordered_trace');check_counterexample(p,c);c['steps'].reverse()
        with self.assertRaises(Rejected):check_counterexample(p,c)
    def test_sample_trap(self):
        p,c=recorded('sampling_trap');r=check_counterexample(p,c)
        self.assertEqual(c['steps'][0]['inputs'],[['3','1']]);self.assertEqual(r['value'],['6','1'])
        for v in (0,1,2):
            d=copy.deepcopy(c);d['steps'][0]['inputs']=[[str(v),'1']]
            with self.assertRaises(Rejected):check_counterexample(p,d)
    def test_empty_trace_parameter_witness(self):
        p,c=recorded('initial_parameter_trap');r=check_counterexample(p,c)
        self.assertEqual(r['length'],0);self.assertEqual(c['parameters'],[['3','1']])
    def test_wrong_input_arity(self):
        p,c=recorded('sampling_trap');c['steps'][0]['inputs']=[]
        with self.assertRaises(Rejected):check_counterexample(p,c)
    def test_certificate_cannot_change_program(self):
        p,c=recorded('nonlinear_mutant_00');p2,_=recorded('nonlinear_equivalence_00')
        with self.assertRaises(Rejected):check_counterexample(p2,c)

class SearchControls(unittest.TestCase):
    def test_zero_generator_budget_unknown(self):
        r=solve(CASES['scaled_graph_00'].system,limits=Limits(generators=0))
        self.assertEqual(r['status'],'unknown');self.assertNotIn('evidence',r)
    def test_zero_pullback_budget_unknown(self):
        self.assertEqual(solve(CASES['scaled_graph_00'].system,limits=Limits(pullbacks=0))['status'],'unknown')
    def test_degree_cap_unknown(self):
        self.assertEqual(solve(CASES['coupled_graph_00'].system,'linear',Limits(degree=3))['status'],'unknown')
    def test_grid_cap_unknown(self):
        self.assertEqual(solve(CASES['sampling_trap'].system,limits=Limits(grid_points=0))['status'],'unknown')
    def test_exact_rational_coefficients(self):
        p=CASES['rational_scaling'].system;r=solve(p)
        self.assertTrue(check_certificate(p.json(),r['evidence'])['accepted'])
    def test_independent_simultaneous_substitution(self):
        x,y=s.symbols('x y');p=x-2*y
        actual=substitute(p,(x,y),(y,x))
        self.assertEqual(s.expand(actual-(y-2*x)),0)
        A=Arithmetic();q=polynomial(poly_json(p,(x,y)),2)
        images=[polynomial(poly_json(y,(x,y)),2),polynomial(poly_json(x,(x,y)),2)]
        self.assertEqual(A.substitute(q,images,2),polynomial(poly_json(y-2*x,(x,y)),2))
    def test_small_random_scalar_differential(self):
        # 80 independent generated scalar transition systems. Check all finite
        # words up to length 3 over {-1,0,1}; this is a bug detector, not a proof.
        rng=random.Random(90177);x,u=s.symbols('x u')
        for k in range(80):
            a,b,c=[rng.randint(-2,2) for _ in range(3)]
            d=0 if k%2==0 else 1
            update=a*x+b*x*x+c*x*u+d*u
            P=System(f'scalar_{k}',(x,),(),1,[(0,(0,))],[Edge(0,0,(u,),(update,))],[(0,x)])
            r=solve(P,limits=Limits(degree=6,seconds=2))
            if d==0:
                self.assertEqual(r['status'],'proved');check_certificate(P.json(),r['evidence'])
            else:
                self.assertEqual(r['status'],'refuted');check_counterexample(P.json(),r['evidence'])
            A=Arithmetic();F=polynomial(P.json()['edges'][0]['update'][0],2)
            seen_bad=False
            for length in range(4):
                for word in itertools.product((-1,0,1),repeat=length):
                    state=Q(0)
                    for v in word:state=A.evaluate(F,[state,Q(v)])
                    seen_bad |= state!=0
            self.assertEqual(seen_bad,d!=0)

if __name__=='__main__':unittest.main(verbosity=2)
