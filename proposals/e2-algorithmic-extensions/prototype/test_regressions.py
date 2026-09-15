"""Small named regression suite, separate from the generated corpus assertions."""
from copy import deepcopy
from fractions import Fraction
from pathlib import Path
import unittest
import sympy as s
import checker
import search

ROOT=Path(__file__).resolve().parents[1]

class RegressionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ps=checker.load(ROOT/'results/problems.json')
        cls.cs=checker.load(ROOT/'results/certificates.json')

    def test_stored_certificates(self):
        for key,p in self.ps.items():
            with self.subTest(key=key):
                self.assertTrue(checker.verify(p,self.cs[key])[0])

    def test_sympy_gosper_adapter(self):
        k=s.Symbol('k',integer=True,positive=True)
        for t in [k*s.factorial(k),1/(k*(k+1)),2**k,k*2**k]:
            with self.subTest(term=t):
                pc=search.sympy_gosper_oracle(t,k)
                self.assertIsNotNone(pc)
                self.assertTrue(checker.verify(*pc)[0])

    def test_zero_target_is_in_empty_span(self):
        pc,_=search.two_sided([],{},2,0)
        self.assertTrue(checker.verify(*pc)[0])

    def test_nonlinear_escape_is_unknown(self):
        x=s.Symbol('x')
        pc,info=search.invariant([x],[],[0],[[x*x]],2,x)
        self.assertIsNone(pc)
        self.assertEqual(info['dimensions'][-1],0)

    def test_substitution_is_simultaneous(self):
        x,y=s.symbols('x y')
        self.assertEqual(search.substitute(x-y,[x,y],[y,x]),y-x)

    def test_scaling_not_conservation(self):
        x,y,z,u,v=s.symbols('x y z u v')
        args=([x,y,z],[u,v],[u,v,u*v],[[2*x,3*y,6*z]],2,z-x*y)
        self.assertFalse(search.conserved(*args))
        self.assertIsNotNone(search.invariant(*args)[0])

    def test_bad_boundary_not_hidden_by_identity(self):
        # Rational identity passes, but R(n,n+1) has zero denominator.
        p,c=self.ps['binomial_square_telescoper'],self.cs['binomial_square_telescoper']
        self.assertTrue(checker.verify(p,c)[0])
        V=checker.poly(c['V'],2)
        zero=checker.subst(V,[{():Fraction(4)},{():Fraction(5)}],0,checker.Work())
        self.assertEqual(zero,{})

    def test_natural_bool_is_not_an_index(self):
        c=deepcopy(self.cs['weyl_commutator_4'])
        c['terms'][0]['relation']=True
        self.assertFalse(checker.verify(self.ps['weyl_commutator_4'],c)[0])

    def test_target_bound_separately(self):
        p=deepcopy(self.ps['weyl_commutator_4'])
        p['target']=[{'m':[],'c':'1'}]
        self.assertFalse(checker.verify(p,self.cs['weyl_commutator_4'])[0])

    def test_duplicate_json_key(self):
        with self.assertRaises(checker.Reject):checker.unique_object([('x',1),('x',2)])

    def test_work_budget(self):
        w=checker.Work();w.left=0
        with self.assertRaises(checker.Reject):checker.mul({(0,):Fraction(1)},{(0,):Fraction(1)},w)

    def test_reversed_words_are_not_equal(self):
        p={'kind':'two_sided','alphabet':2,'relations':[[{'m':[0,1],'c':'1'}]],
           'target':[{'m':[1,0],'c':'1'}]}
        c={'kind':'two_sided','terms':[{'relation':0,'left':[],'right':[],'coefficient':'1'}]}
        self.assertFalse(checker.verify(p,c)[0])

    def test_false_goal_not_solved(self):
        x=s.Symbol('x')
        pc,_=search.invariant([x],[],[0],[[x+1]],2,x)
        self.assertIsNone(pc)

if __name__=='__main__':unittest.main(verbosity=2)
