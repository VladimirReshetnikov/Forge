"""Small standard-library unit suite; larger generated suites live in results/."""
import unittest
from fractions import Fraction as Q
from real_fibers.exact import P,Reject,Limit,poly,rat,signature_from_signs
from real_fibers.logic import indicator,eval_formula
from real_fibers.checker import Fiber,verify
from real_fibers.sturm import root_count,root_product,to_sparse
from real_fibers.witness import verify_witness

class CoreTests(unittest.TestCase):
    def test_fraction_is_exact(self):self.assertEqual(rat([1,3]),Q(1,3))
    def test_float_refused(self):
        with self.assertRaises(Reject):rat([0.5,1])
    def test_unreduced_rational_refused(self):
        with self.assertRaises(Reject):rat([2,4])
    def test_bool_refused(self):
        with self.assertRaises(Reject):rat([True,1])
    def test_duplicate_monomial_refused(self):
        with self.assertRaises(Reject):poly([[[0],[1,1]],[[0],[1,1]]],1)
    def test_polynomial_identity(self):
        x=P.var(1,0);self.assertEqual((x+1)**2,x*x+2*x+1)
    def test_empty_signature(self):self.assertEqual(signature_from_signs([1,0,0]),0)
    def test_indefinite_signature(self):self.assertEqual(signature_from_signs([1,0,-1]),0)
    def test_positive_signature(self):self.assertEqual(signature_from_signs([1,-1,1]),2)
    def test_raw_coefficients_are_not_signs(self):
        with self.assertRaises(Reject):signature_from_signs([1,2,1])
    def test_negative_signature(self):self.assertEqual(signature_from_signs([1,1,1]),-2)
    def test_single_zero_eigenvalue(self):self.assertEqual(signature_from_signs([1,-1,0]),1)
    def test_repeated_root(self):self.assertEqual(root_count((0,0,1)),1)
    def test_no_real_root(self):self.assertEqual(root_count((1,0,1)),0)
    def test_two_real_roots(self):self.assertEqual(root_count((-2,0,1)),2)
    def test_endpoint_root_refused(self):
        with self.assertRaises(Reject):root_count((-1,1),Q(1),Q(2))
    def test_finite_isolator(self):self.assertEqual(root_count((-2,0,1),Q(1),Q(2)),1)
    def test_squarefree_union(self):
        x=P.var(1,0);p=root_product([x*x,(x-1)**4]);self.assertEqual(root_count(p),2)
    def test_zero_atom_indicator(self):
        p=indicator(['atom',0,'eq'],1);self.assertEqual([p.eval([i]) for i in [-1,0,1]],[0,1,0])
    def test_strict_atom_indicator(self):
        p=indicator(['atom',0,'gt'],1);self.assertEqual([p.eval([i]) for i in [-1,0,1]],[0,0,1])
    def test_correlated_boolean_algebra(self):
        f=['and',['atom',0,'gt'],['atom',0,'lt']];self.assertFalse(indicator(f,1))
    def test_nonmonic_refused(self):
        p={'schema':'forge-real-fiber-v1','parameters':0,'degrees':[2],
           'equations':[(2*P.var(1,0)**2).data()],'atoms':[],'formula':['true']}
        with self.assertRaises(Reject):Fiber.parse(p)
    def test_dimension_cap_is_not_refutation(self):
        p={'schema':'forge-real-fiber-v1','parameters':0,'degrees':[4,4],
           'equations':[],'atoms':[],'formula':['true']}
        with self.assertRaises(Limit):Fiber.parse(p)
    def test_nonlinear_triangular_reduction(self):
        x,y=P.var(2,0),P.var(2,1)
        p={'schema':'forge-real-fiber-v1','parameters':0,'degrees':[2,2],
           'equations':[(x*x-2).data(),(y*y-x).data()],'atoms':[],'formula':['true']}
        f=Fiber.parse(p);self.assertEqual(f.reduce(y**4),P.const(2,2))
    def test_witness_is_algebraic(self):
        x=P.var(1,0);p={'schema':'forge-real-fiber-v1','parameters':0,'degrees':[2],
          'equations':[(x*x-2).data()],'atoms':[x.data()],'formula':['atom',0,'gt']}
        c={'schema':'algebraic-witness-v1','interval':[[1,1],[2,1]]}
        self.assertEqual(verify_witness(p,c)['atom_signs'],[1])

if __name__=='__main__':unittest.main()
