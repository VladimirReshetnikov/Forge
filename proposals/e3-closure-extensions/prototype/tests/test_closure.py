"""Boundary and algebra tests in addition to the recorded experiment corpus."""
import copy, itertools, json, random, unittest
from fractions import Fraction
from pathlib import Path
import sympy as sp
from forge_closure import checker as ck
from forge_closure.search import (make_problem, pullback_search, ideal_search,
    ClosureLimits, wire_poly, expression, telescoper_search, make_moment, ideal_coordinates)

ROOT=Path(__file__).resolve().parents[2]

class BoundaryTests(unittest.TestCase):
    def test_replay_entire_recorded_corpus(self):
        files=sorted((ROOT/'results'/'certificates').glob('*.json'))
        self.assertEqual(len(files),313)
        for p in files:
            with self.subTest(case=p.stem):
                b=json.loads(p.read_text()); self.assertTrue(ck.verify(b['problem'],b['certificate']))
    def test_nonobjects_rejected(self):
        for a,b in [(None,{}),({},None),([],[]),({}, {'kind':'bogus'})]:
            with self.assertRaises(ck.Invalid):ck.verify(a,b)
    def test_exact_rational_gate(self):
        for q in [[0,0],[1,-1],[2,4],[0,2],[True,1],[1.,1],[1,True],'1/2']:
            with self.assertRaises(ck.Invalid):ck.rat(q)
        self.assertEqual(ck.rat([-3,7]),Fraction(-3,7))
    def test_polynomial_gate(self):
        for p in [[[[1],[0,1]]],[[[-1],[1,1]]],[[[1,0],[1,1]]],[[[1],[1,1]],[[1],[2,1]]]]:
            with self.assertRaises(ck.Invalid):ck.poly(p,1)
    def test_zero_target_needs_no_basis(self):
        x=sp.symbols('x'); p=make_problem((x,),[(x*x+1,)],(0,),[sp.Integer(0)])
        for engine in [pullback_search,ideal_search]:
            r=engine(p); self.assertEqual(r['status'],'proved'); self.assertEqual(r['certificate']['basis'],[])
    def test_false_target_at_empty_word(self):
        x=sp.symbols('x');p=make_problem((x,),[(x+1,)],(1,),[x])
        for engine in [pullback_search,ideal_search]:
            r=engine(p); self.assertEqual(r['status'],'refuted'); self.assertEqual(r['certificate']['word'],[])
    def test_noncanonical_origins_not_authority(self):
        b=json.loads((ROOT/'results/certificates/coupled_quadratic.json').read_text())
        b['certificate']['origins']=[{'untrusted_annotation':True}]
        self.assertTrue(ck.verify(b['problem'],b['certificate']))
    def test_simultaneous_substitution(self):
        x,y=sp.symbols('x y'); p=ck.poly(wire_poly(x,(x,y)),2)
        fs=[ck.poly(wire_poly(y,(x,y)),2),ck.poly(wire_poly(x+y,(x,y)),2)]
        self.assertEqual(ck.subst(p,fs,2),ck.poly(wire_poly(y,(x,y)),2))
    def test_fixed_generator_linear_reconstruction(self):
        x,y=sp.symbols('x y'); basis=[x*x-y,x*y-1];q=y*y-x
        cs=ideal_coordinates(q,basis,(x,y),max_degree=3)
        self.assertIsNotNone(cs)
        self.assertEqual(sp.expand(sum(c*b for c,b in zip(cs,basis))-q),0)
    def test_multiplier_cap_is_unknown(self):
        x,y=sp.symbols('x y');p=make_problem((x,y),[(x**4,y**4)],(1,1),[x-y])
        self.assertEqual(ideal_search(p,multiplier_degree=0)['status'],'unknown')
    def test_basis_cap_is_unknown(self):
        x,y=sp.symbols('x y');p=make_problem((x,y),[(y,x+y)],(0,0),[x])
        self.assertEqual(pullback_search(p,ClosureLimits(basis=1))['status'],'unknown')
    def test_rational_polynomial_arithmetic_differential(self):
        # 200 exact cases; compare independent operations against SymPy.
        rng=random.Random(731); x,y=sp.symbols('x y')
        for i in range(200):
            def random_poly():return sp.expand(sum(sp.Rational(rng.randrange(-4,5),rng.randrange(1,6))*x**a*y**b for a in range(4) for b in range(4-a)))
            p,q=random_poly(),random_poly()
            cp,cq=ck.poly(wire_poly(p,(x,y)),2),ck.poly(wire_poly(q,(x,y)),2)
            self.assertEqual(ck.add(cp,cq),ck.poly(wire_poly(p+q,(x,y)),2))
            self.assertEqual(ck.mul(cp,cq),ck.poly(wire_poly(p*q,(x,y)),2))
            images=[x+y,x-y+1]
            expected=p.subs(dict(zip((x,y),images)),simultaneous=True)
            self.assertEqual(ck.subst(cp,[ck.poly(wire_poly(z,(x,y)),2) for z in images],2),ck.poly(wire_poly(expected,(x,y)),2))

if __name__=='__main__':unittest.main()
