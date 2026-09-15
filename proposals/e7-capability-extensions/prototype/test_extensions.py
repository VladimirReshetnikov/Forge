"""Portable regression suite. Run with python -S -m unittest discover ... ."""
from copy import deepcopy
from dataclasses import replace
from fractions import Fraction
from pathlib import Path
import json
import unittest

import continuation_synth as cs
import cyclic_rank as cr
from exact import *
from invariant_space import *
import ideal_closure as ic
from replay import (check_space,check_rank,check_church_index,check_ideal,
                    check_orbit_counterexample,rational,Rejected)

ROOT=Path(__file__).resolve().parents[1]

class ExactAlgebraTests(unittest.TestCase):
    def test_empty_nullspace(self):
        self.assertEqual(nullspace([],2),[[Q(1),Q(0)],[Q(0),Q(1)]])
    def test_inconsistent_coordinates(self):
        self.assertIsNone(coordinates([[Q(1),Q(0)]],[Q(0),Q(1)]))
    def test_substitution_keeps_degree(self):
        x=var(1,0)
        self.assertEqual(subst(x,[mul(x,x)],1),{(2,):Q(1)})
        with self.assertRaises(ValueError):vector(subst(x,[mul(x,x)],1),monomials(1,1))
    def test_polynomial_cancellation(self):
        x,y=var(2,0),var(2,1)
        self.assertEqual(mul(add(x,y),add(x,scale(-1,y))),add(mul(x,x),scale(-1,mul(y,y))))
    def test_noncanonical_rational_rejected(self):
        for v in ([2,2],[0,2],[1,-2],[True,1],0.5):
            with self.subTest(v=v),self.assertRaises(Rejected):rational(v)

class InvariantTests(unittest.TestCase):
    def test_coupled_not_conserved(self):
        p=coupled_example();c,m=discover(p)
        self.assertEqual(m['dimensions'],[5,2]);self.assertEqual(conserved_dimension(p),0)
        self.assertTrue(check_space(p.encoded(),c)[0])
    def test_degree_one_misses_coupling(self):
        _,m=discover(replace(coupled_example(),degree=1))
        self.assertFalse(m['target_in_span'])
    def test_space_growth_limitation(self):
        x=var(1,0);p=Problem('growth',1,1,0,[const(0,0)],[[mul(x,x)]],x)
        c,m=discover(p);self.assertEqual(m['fixed_point_dimension'],0)
        self.assertFalse(check_space(p.encoded(),c)[0])
        self.assertTrue(check_space(p.encoded(),c,require_target=False)[0])
    def test_ideal_handles_growth(self):
        p=next(ic.fixtures());c,m=ic.complete(p)
        self.assertEqual(m['status'],'found');self.assertTrue(check_ideal(p.encoded(),c)[0])
    def test_ideal_budget_not_refutation(self):
        c,m=ic.complete(coupled_example(),max_generators=1)
        self.assertIsNone(c);self.assertEqual(m['status'],'unknown')
    def test_orbit_word_direction(self):
        p=list(ic.fixtures())[-1];c,m=ic.complete(p)
        self.assertEqual(c['word'],[1,0]);self.assertTrue(check_orbit_counterexample(p.encoded(),c)[0])
        c['word'].reverse();self.assertFalse(check_orbit_counterexample(p.encoded(),c)[0])
    def test_initial_violation_zero_steps(self):
        x=var(1,0);p=Problem('initial',1,1,0,[const(0,1)],[[x]],x)
        c,m=ic.complete(p);self.assertEqual(c['word'],[])
        self.assertTrue(check_orbit_counterexample(p.encoded(),c)[0])
    def test_traced_groebner_pair(self):
        x,y=var(2,0),var(2,1);orig=[add(mul(x,y),const(2,-1)),add(mul(y,y),scale(-1,x))]
        gs,rs,count=ic.groebner_traced(orig,2);self.assertGreater(count,0)
        for g,row in zip(gs,rs):
            self.assertEqual(g,add(*(mul(a,b) for a,b in zip(row,orig))))
    def test_zero_target(self):
        p=replace(coupled_example(),target={});c,m=ic.complete(p)
        self.assertTrue(check_ideal(p.encoded(),c)[0])

class SynthesisTests(unittest.TestCase):
    def test_elimination_spine_order(self):
        r=cs.carrier_from_elimination_spine(cs.ELEM,[cs.INT,cs.ELEM])
        self.assertEqual(r,cs.arrow(cs.INT,cs.arrow(cs.ELEM,cs.ELEM)))
    def test_local_and_flat_identical(self):
        a,am=cs.synthesize(4,False);b,bm=cs.synthesize(4,True)
        self.assertEqual(a,b);self.assertEqual(am['complete_candidates'],2148)
        self.assertEqual(bm['complete_candidates'],1)
    def test_symbolic_contract(self):
        t,_=cs.synthesize(0,True);e=cs.certificate(t,0)
        self.assertTrue(check_church_index(e['problem'],e['certificate'])[0])
    def test_type_error(self):
        with self.assertRaises(TypeError):cs.infer(cs.app(cs.V('x'),cs.V('x')),{'x':cs.INT})
    def test_escaped_variable(self):
        with self.assertRaises(TypeError):cs.infer(cs.V('futureBinder'),{})
    def test_capture(self):
        with self.assertRaises(TypeError):cs.infer(cs.lam('x',cs.INT,cs.V('x')),{'x':cs.INT})
    def test_negative_and_huge_indices(self):
        t,_=cs.synthesize(0,True)
        for i in [-2**80,-1,0,1,2,2**80]:
            self.assertEqual(cs.execute(t,99,[4,5],i,0),cs.reference_index(99,[4,5],i))
    def test_cutoff(self):
        t,m=cs.synthesize(12,False,256)
        self.assertIsNone(t);self.assertEqual(m['status'],'truncated')

class DescentTests(unittest.TestCase):
    def test_phase_rank(self):
        p=cr.fixtures()[0];c,m=cr.synthesize(p)
        self.assertEqual(c['layers'],[{'P':[1,2],'Q':[0,2]}])
        self.assertTrue(check_rank(p,c)[0])
    def test_lex_rank(self):
        p=cr.fixtures()[3];c,m=cr.synthesize(p)
        self.assertEqual(m['mode'],'lexicographic');self.assertTrue(check_rank(p,c)[0])
    def test_strictness_not_nonincrease(self):
        good=cr.fixtures()[0];c,m=cr.synthesize(good)
        bad=deepcopy(good);bad['edges'][1]['updates'][0][0]=0
        self.assertFalse(check_rank(bad,c)[0])
    def test_bad_alternation(self):
        p=cr.fixtures()[-1];c,m=cr.synthesize(p)
        self.assertIsNone(c);self.assertFalse(cr.size_change(p)['criterion_met'])
        # Concrete infinite two-cycle: (1,0)->(0,1)->(1,0).
        self.assertEqual((1-1,0+1),(0,1));self.assertEqual((0+1,1-1),(1,0))
    def test_size_change_composition(self):
        # A cross-thread strict descent cannot be replaced by two diagonal tests.
        g=(0,2,1,0);gg=cr.compose(g,g,2)
        self.assertEqual(gg,(2,0,0,2))

class RecordedEvidenceTests(unittest.TestCase):
    def test_all_recorded_certificates(self):
        data=json.loads((ROOT/'results'/'certificates.json').read_text())
        checks={'pullback-space-v1':check_space,'ranking-v1':check_rank,
                'church-index-v1':check_church_index,'pullback-ideal-v1':check_ideal,
                'polynomial-orbit-counterexample-v1':check_orbit_counterexample}
        self.assertEqual(len(data['certificates']),135)
        for e in data['certificates']:
            with self.subTest(name=e['problem']['name']):
                self.assertTrue(checks[e['certificate']['kind']](e['problem'],e['certificate'])[0])
    def test_mutation_receipts(self):
        r=json.loads((ROOT/'results'/'results.json').read_text())
        self.assertEqual(len(r['mutations']),31)
        self.assertTrue(all(not e['accepted'] for e in r['mutations']))

if __name__=='__main__':unittest.main()
