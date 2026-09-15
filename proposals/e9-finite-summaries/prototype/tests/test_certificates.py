import unittest,copy,json
from fractions import Fraction as Q
import sympy as s
from forge_summaries.exact import *
from forge_summaries.check import *
from forge_summaries.linear_search import search,model,polynomial_input_search
from forge_summaries.telescoping_search import attempt,poly,n,k
from forge_summaries.ore_search import common_left_multiple,singularity_cover
from forge_summaries.lift import compile_lift
from replay import no_duplicates

class Decoding(unittest.TestCase):
    def test_rational_roundtrip(self): self.assertEqual(rational(encq(Q(-3,7))),Q(-3,7))
    def test_float(self):
        with self.assertRaises(Invalid): rational([1.0,2])
    def test_bool(self):
        with self.assertRaises(Invalid): rational([True,1])
    def test_zero_denominator(self):
        with self.assertRaises(Invalid): rational([1,0])
    def test_noncanonical(self):
        with self.assertRaises(Invalid): rational([2,4])
    def test_negative_denominator(self):
        with self.assertRaises(Invalid): rational([1,-2])
    def test_duplicate_terms(self):
        with self.assertRaises(Invalid): decode_poly([[0,0,1,1],[0,0,1,1]])
    def test_duplicate_json_keys(self):
        with self.assertRaises(ValueError): json.loads('{"a":1,"a":2}',object_pairs_hook=no_duplicates)
    def test_univariate_guard(self):
        with self.assertRaises(Invalid): decode_operator([[[0,1,1,1]]])
    def test_explicit_zero(self):
        with self.assertRaises(Invalid): decode_poly([[0,0,0,1]])
    def test_bad_checker_kind(self): self.assertFalse(verify_bundle({'checker':[],'problem':{},'certificate':{}}))
    def test_degree_cap(self):
        with self.assertRaises(Invalid): decode_poly([[129,0,1,1]])

class WordCertificates(unittest.TestCase):
    def setUp(self):
        self.u=[1,1];self.v=[1,-1];self.ms=[[[2,0],[0,2]],[[3,0],[0,3]]]
        self.p=model(self.u,self.ms,self.v);self.c,_=search(self.u,self.ms,self.v)
    def test_valid(self): self.assertTrue(linear(self.p,self.c))
    def test_initial_binding(self):
        p=copy.deepcopy(self.p);p['initial'][0]=[2,1];self.assertFalse(linear(p,self.c))
    def test_output_binding(self):
        p=copy.deepcopy(self.p);p['output'][0]=[2,1];self.assertFalse(linear(p,self.c))
    def test_transition_binding(self):
        p=copy.deepcopy(self.p);p['transitions'][0][0][0]=[4,1];self.assertFalse(linear(p,self.c))
    def test_missing_letter(self):
        c=copy.deepcopy(self.c);c['actions'].pop();self.assertFalse(linear(self.p,c))
    def test_bad_coordinates(self):
        c=copy.deepcopy(self.c);c['initial_coordinates'][0]=[2,1];self.assertFalse(linear(self.p,c))
    def test_extra_field(self):
        c=copy.deepcopy(self.c);c['trusted']=True;self.assertFalse(linear(self.p,c))
    def test_zero_initial_rank_zero(self):
        u=[0,0];c,_=search(u,self.ms,self.v);self.assertTrue(linear(model(u,self.ms,self.v),c));self.assertEqual(c['basis'],[])
    def test_empty_counterexample(self):
        c,_=search([1],[[[3]]],[2]);self.assertEqual(c['word'],[]);self.assertTrue(counterexample(model([1],[[[3]]],[2]),c))
    def test_counterexample_fake_zero(self):
        c,_=search([1],[[[3]]],[2]);c['value']=[0,1];self.assertFalse(counterexample(model([1],[[[3]]],[2]),c))
    def test_nonaffine_lift_refused(self):
        a=s.Symbol('a')
        with self.assertRaises(ValueError): compile_lift([a],[0],[[a*a]],a,1)
    def test_observer_degree_refused(self):
        a=s.Symbol('a')
        with self.assertRaises(ValueError): compile_lift([a],[0],[[a+1]],a*a,1)
    def test_polynomial_input_degree_trap(self):
        a,x=s.symbols('a x');u,co,v,_=compile_lift([a],[0],[[a+x*(x-1)]],a,1,x)
        c,_=polynomial_input_search(u,co,v);self.assertEqual(c['word'],[2])

class TelescopeCertificates(unittest.TestCase):
    def test_franel(self):
        c,_=attempt(3,1,2,2,2);self.assertTrue(telescoper({'kind':'binomial-power-sum','power':3,'weight':[1,1]},c))
    def test_q_zero(self):
        c,_=attempt(2,0,2,1,1);self.assertIsNotNone(c);self.assertTrue(telescoper({'kind':'binomial-power-sum','power':2,'weight':[0,1]},c))
    def test_parameter_misbinding(self):
        c,_=attempt(2,1,1,1,1);self.assertFalse(telescoper({'kind':'binomial-power-sum','power':2,'weight':[2,1]},c))
    def test_changed_flux(self):
        c,_=attempt(2,1,1,1,1);c['flux'][0]=encpoly(add(decode_poly(c['flux'][0]),const(1)))
        self.assertFalse(telescoper({'kind':'binomial-power-sum','power':2,'weight':[1,1]},c))
    def test_missing_flux(self):
        c,_=attempt(2,1,1,1,1);c['flux']=[];self.assertFalse(telescoper({'kind':'binomial-power-sum','power':2,'weight':[1,1]},c))
    def test_zero_operator(self):
        c,_=attempt(2,1,1,1,1);c['operator']=[[],[]];self.assertFalse(telescoper({'kind':'binomial-power-sum','power':2,'weight':[1,1]},c))
    def test_insufficient_ansatz_unknown(self):
        c,st=attempt(3,1,1,1,1);self.assertIsNone(c);self.assertEqual(st['nullity'],0)

class OreAndSeeds(unittest.TestCase):
    def test_noncommutative(self):
        self.assertEqual(ore_mul([{},const(1)],[mon(1)]),[{},add(mon(1),const(1))])
        self.assertNotEqual(ore_mul([{},const(1)],[mon(1)]),ore_mul([mon(1)],[{},const(1)]))
    def test_zero_coefficient_search_regression(self):
        a=[{},const(1)];b=[const(-5),const(1)];c,_=common_left_multiple(a,b,1,0)
        self.assertTrue(ore_identity({'kind':'common-left-multiple','left':[encpoly(z) for z in a],
                                     'right':[encpoly(z) for z in b]},c))
    def test_singularity_reset(self):
        a=[scale(poly(n-5),-2),poly(n-5)];c=singularity_cover(a);self.assertEqual(c['seed_indices'],[0,6])
    def test_missing_reset(self):
        a=[scale(poly(n-5),-2),poly(n-5)];c=singularity_cover(a);c['seed_indices']=[0]
        self.assertFalse(singularity_plan({'kind':'recurrence-equality-plan','operator':[encpoly(z) for z in a]},c))
    def test_missing_root(self):
        a=[{},poly(n*(n-3))];c=singularity_cover(a);c['singular_indices']=[0]
        self.assertFalse(singularity_plan({'kind':'recurrence-equality-plan','operator':[encpoly(z) for z in a]},c))
    def test_understated_root_bound(self):
        a=[{},poly(n-5)];c=singularity_cover(a);c['bound']=1
        self.assertFalse(singularity_plan({'kind':'recurrence-equality-plan','operator':[encpoly(z) for z in a]},c))
    def test_constant_lead(self):
        a=[const(-2),const(1)];c=singularity_cover(a);self.assertEqual(c['seed_indices'],[0]);self.assertEqual(c['bound'],0)
    def test_roots_beyond_resource_limit_unknown(self): self.assertIsNone(singularity_cover([{},poly(n-100001)]))
    def test_initial_values_not_enough_countermodel(self):
        # Both sequences solve (n-5)(E-2), agree through index 5, differ at 6.
        f=lambda n:0
        g=lambda n:0 if n<6 else 2**(n-6)
        for t in range(20):
            self.assertEqual((t-5)*(g(t+1)-2*g(t)),0)
        self.assertTrue(all(f(t)==g(t) for t in range(6)));self.assertNotEqual(f(6),g(6))

if __name__=='__main__': unittest.main()
