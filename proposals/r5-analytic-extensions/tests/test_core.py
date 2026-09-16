"""Standard-library unit tests. Run with python -m unittest discover -s tests -v."""
import copy,json,random,sys,unittest
from pathlib import Path
from fractions import Fraction as Q
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'prototype'))
from forge_analytic import algebra as A,jets as J,ladders as L,tails as T
from forge_analytic.checker import verify,loads,rat,Rejected

class AlgebraTests(unittest.TestCase):
    def test_shift_evaluation(self):
        r=random.Random(17)
        for _ in range(100):
            p=A.poly(r.randint(-8,8) for _ in range(7)); N=r.randint(-5,5)
            for x in (-2,0,3):self.assertEqual(A.evaluate(A.shift(p,N),x),A.evaluate(p,x+N))
    def test_shift_positive(self):
        r=random.Random(18)
        for _ in range(200):
            p=A.poly([r.randint(-30,30) for _ in range(r.randint(0,12))]+[r.randint(1,10)])
            self.assertTrue(all(c>0 for c in A.shift(p,A.positive_shift_cutoff(p))))
    def test_interval_dependency(self):
        self.assertEqual(A.horner(A.poly([0,-1,1]),Q(1)),(Q(-1),Q(0)))
    def test_dense_product(self):
        self.assertEqual(A.mul(A.poly([1,2]),A.poly([3,4])),A.poly([3,10,8]))

class AnalyticTests(unittest.TestCase):
    def setUp(self):self.expr=J.minus(J.P(0,1),J.atom('sin'))
    def test_sine(self):
        c=J.search(self.expr,Q(1,2));self.assertIsNotNone(c)
        self.assertEqual(c['order'],4);self.assertEqual(c['valuation'],3)
        self.assertEqual(Q(c['margin']),Q(31,216));self.assertTrue(verify(c['subject'],c))
    def test_false_sine(self):self.assertIsNone(J.search(['neg',self.expr],Q(1,2),14))
    def test_anchor_zero(self):
        c=J.search(J.P(0,0,0,1),Q(1,2));self.assertTrue(verify(c['subject'],c))
    def test_guard(self):self.assertIsNone(J.search(J.atom('log1p',-1),2))
    def test_zero(self):
        c=J.search(J.P(0));self.assertTrue(verify(c['subject'],c))
    def test_trigonometric_identity_unknown(self):
        s,c=J.atom('sin'),J.atom('cos')
        self.assertIsNone(J.search(J.minus(J.plus(J.times(s,s),J.times(c,c)),J.P(1)),Q(1,2),14))
    def test_external_subject(self):
        c=J.search(self.expr,Q(1,2));s=copy.deepcopy(c['subject']);s['b']='3/4'
        self.assertFalse(verify(s,c))
    def test_noncanonical_rational(self):
        for q in ('2/2','1','0.5','1/0','+1/2','01/2'):
            with self.assertRaises(ValueError):rat(q)

class LadderTests(unittest.TestCase):
    def test_global_exp(self):
        f={Q(1):A.poly([1]),Q(0):A.poly([-1,-1])};c=L.search(f)
        self.assertEqual(c['rates'],['1/1']);self.assertTrue(verify(c['subject'],c))
    def test_lift_identity(self):
        g={Q(1):A.poly([1,3,2]),Q(0):A.poly([4,1])}
        for rate in (Q(-1),Q(0),Q(1),Q(2)):
            f=L.lift(g,rate,Q(3,4));self.assertEqual(L.apply(f,rate),g);self.assertEqual(L.seed(f),Q(3,4))
    def test_negative_seed(self):self.assertIsNone(L.search({Q(1):A.poly([-1])}))
    def test_even_root(self):
        self.assertIsNone(L.search({Q(2):A.poly([1]),Q(1):A.poly([-4]),Q(0):A.poly([4])},8))

class TailTests(unittest.TestCase):
    def test_harmonic(self):
        c=T.synthesize(A.poly([1]),A.poly([0,1]));self.assertEqual(c['kind'],'divergence');self.assertTrue(verify(c['subject'],c))
    def test_inverse_square(self):
        c=T.optimized_barrier(A.poly([1]),A.poly([0,0,1]),2)
        self.assertEqual(c['tail_bound'],'3/4');self.assertTrue(verify(c['subject'],c))
    def test_tight_telescoper(self):
        c=T.make_barrier(A.poly([1]),A.poly([0,1,1]),1,0,1,Q(1))
        self.assertEqual(c['shifted_residual'],['0/1']);self.assertTrue(verify(c['subject'],c))
    def test_harmonic_no_barrier(self):self.assertIsNone(T.optimized_barrier(A.poly([1]),A.poly([0,1]),2))
    def test_strict_modulus(self):
        c=T.synthesize(A.poly([1]),A.poly([0,0,1]))
        for eps in (Q(1),Q(1,1000),Q(3,4)):
            k=T.modulus(c,eps);self.assertLess(Q(c['constant'])/Q(k+c['shift'])**c['power'],eps)
            exact=T.minimal_modulus(c,eps);self.assertLessEqual(exact,k)
        for bad_power in (0,True,17):
            bad=copy.deepcopy(c);bad['power']=bad_power
            with self.assertRaises(ValueError):T.modulus(bad,Q(1))
            with self.assertRaises(ValueError):T.minimal_modulus(bad,Q(1))
    def test_boolean_cutoff_rejected(self):
        c=T.synthesize(A.poly([1]),A.poly([0,0,1]));c['cutoff']=True;self.assertFalse(verify(c['subject'],c))
    def test_pole_at_cutoff_rejected(self):
        c=T.make_barrier(A.poly([1]),A.poly([-1,1]),1,0,1,Q(10));self.assertFalse(verify(c['subject'],c))
    def test_malformed_json(self):
        for data in ('{"x":0,"x":1}','{"x":Infinity}','{"x":1.0}','[]'):
            with self.assertRaises(ValueError):loads(data)
    def test_all_saved(self):
        d=ROOT/'results/run-01';problems=loads((d/'problems.json').read_text());certs=loads((d/'certificates.json').read_text())
        self.assertEqual(set(problems),set(certs))
        for key,p in problems.items():self.assertTrue(verify(p['subject'],certs[key]),key)

if __name__=='__main__':unittest.main()
