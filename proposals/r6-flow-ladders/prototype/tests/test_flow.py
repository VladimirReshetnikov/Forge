import copy
import itertools
import random
import unittest
from fractions import Fraction as F
from forge_flow.model import ExpPoly as E
from forge_flow.search import (canonical_search,ladder_search,optimal_ladder,system_search,
                               make_ladder,prove)
from forge_flow.check import (check_ladder,check_obstruction,check_minimality,check_system,
                              decode,derivative)
from forge_flow.enclosure import exp_bound,check_root,check_refutation,evaluate,reciprocal,power
from forge_flow.witness_search import root,refute


class FlowTests(unittest.TestCase):
    def test_exact_derivative(self):
        f=E.make({F(2,3):[1,2,3],-1:[4]})
        self.assertEqual(decode(f.deriv().payload()),derivative(decode(f.payload())))

    def test_canonical_normalization(self):
        self.assertEqual(E.make({0:[0,0],1:[1,0]}),E.make({1:[1]}))

    def test_zero(self):
        f=E.zero();r=optimal_ladder(f)
        self.assertEqual(r['steps'],0)
        self.assertTrue(check_minimality(f.problem(),r['certificate'],r['minimality']))

    def test_float_rejected(self):
        with self.assertRaises(TypeError):E.make({1:[1.0]})
        f=E.make({1:[1],0:[-1]});r=optimal_ladder(f)
        p=f.problem();p['terms'][0]['coeffs'][0]=[-1.0,1]
        self.assertFalse(check_ladder(p,r['certificate']))

    def test_boolean_rejected(self):
        f=E.make({1:[1],0:[-1]});r=optimal_ladder(f);p=f.problem()
        p['terms'][0]['coeffs'][0]=[True,1]
        self.assertFalse(check_ladder(p,r['certificate']))

    def test_nonreduced_rejected(self):
        f=E.make({1:[1],0:[-1]});r=optimal_ladder(f);p=f.problem()
        p['terms'][0]['coeffs'][0]=[-2,2]
        self.assertFalse(check_ladder(p,r['certificate']))

    def test_duplicate_rate_rejected(self):
        f=E.make({1:[1]});r=optimal_ladder(f);p=f.problem()
        p['terms'].append(copy.deepcopy(p['terms'][0]))
        self.assertFalse(check_ladder(p,r['certificate']))

    def test_wrong_anchor_and_direction(self):
        f=E.make({1:[1],0:[-1]});c=optimal_ladder(f)['certificate']
        for key,value in [('anchor',[1,1]),('direction','left')]:
            p=f.problem();p[key]=value
            self.assertFalse(check_ladder(p,c))

    def test_external_target_binding(self):
        f=E.make({1:[1],0:[-1]});c=optimal_ladder(f)['certificate']
        self.assertFalse(check_ladder(E.make({1:[1],0:[-2]}).problem(),c))

    def test_terminal_corruption(self):
        f=E.make({1:[1],0:[-1,0,F(-1,2)]});c=optimal_ladder(f)['certificate']
        c['terminal']=E.make({0:[999]}).payload()
        self.assertFalse(check_ladder(f.problem(),c))

    def test_obstruction_is_not_refutation(self):
        f=E.make({2:[1],1:[-4],0:[4]});r=canonical_search(f)
        self.assertEqual(r['status'],'no_ladder')
        self.assertTrue(check_obstruction(f.problem(),r['certificate']))
        self.assertFalse(check_refutation(f.problem(),r['certificate']))
        self.assertEqual(refute(f)['status'],'unknown')

    def test_minimum_zeros_zero_one_two_three(self):
        cases=[(E.make({1:[1],0:[-1,-1]}),0),
               (E.make({1:[1],0:[0,F(-1,2),F(-1,4)]}),1),
               (E.make({1:[1],0:[0,0,F(-1,4)]}),2),
               (E.make({1:[1],0:[1,0,1]}),3)]
        for f,z in cases:
            r=optimal_ladder(f);b=ladder_search(f)
            self.assertEqual(r['minimality']['zeros'],z)
            self.assertEqual(r['steps'],len(b['certificate']['cofactors']))
            self.assertTrue(check_minimality(f.problem(),r['certificate'],r['minimality']))

    def test_forged_minimality(self):
        f=E.make({1:[1],0:[1,0,1]});r=optimal_ladder(f)
        bad=copy.deepcopy(r['minimality']);bad['zeros']=0;bad['previous_failure']=None
        self.assertFalse(check_minimality(f.problem(),r['certificate'],bad))

    def test_budget_does_not_erase_proof(self):
        f=E.make({1:[1],0:[-1,-1,F(-1,2)]})
        self.assertEqual(ladder_search(f,max_states=1)['status'],'unknown_budget')
        r=prove(f,compression_budget=1)
        self.assertEqual(r['status'],'certificate')
        self.assertTrue(check_ladder(f.problem(),r['certificate']))

    def test_positive_system_cycle(self):
        H=[E.make({1:[F(1,2)],-1:[F(-1,2)],0:[0,-1]}),
           E.make({1:[F(1,2)],-1:[F(1,2)],0:[-1]})]
        c=system_search(H)['certificate']
        self.assertTrue(check_system([h.problem() for h in H],c))
        c['matrix'][0][1]=[-1,1]
        self.assertFalse(check_system([h.problem() for h in H],c))

    def test_exp_zero_and_inverse(self):
        self.assertEqual(exp_bound(F(0)),(F(1),F(1)))
        x=exp_bound(F(1,3));y=exp_bound(F(-1,3))
        self.assertEqual(y,(1/x[1],1/x[0]))

    def test_enclosure_guards(self):
        for n in [-1,65,True]:
            with self.assertRaises(ValueError):exp_bound(F(1),n)
        with self.assertRaises(ValueError):reciprocal((F(-1),F(1)))
        self.assertEqual(power((F(-2),F(1)),2),(F(0),F(4)))

    def test_negative_point(self):
        f=E.make({1:[1],0:[-1,-2]});c=refute(f)['certificate']
        self.assertTrue(check_refutation(f.problem(),c))
        c['point']=[-1,1]
        self.assertFalse(check_refutation(f.problem(),c))

    def test_root_and_wrong_domain(self):
        f=E.make({1:[1],0:[-1,-2]});r=root(f,F(1),F(3,2))
        self.assertTrue(check_root(r['problem'],r['certificate']))
        p=copy.deepcopy(r['problem']);p['interval']=[[2,1],[3,1]]
        self.assertFalse(check_root(p,r['certificate']))

    def test_fake_cover_and_endpoint_root(self):
        f=E.make({1:[1],0:[-1,-2]});r=root(f,F(1),F(3,2));c=r['certificate']
        leaf=copy.deepcopy(c['derivative_cover'])
        c['derivative_cover']={'kind':'split','cut':[1,1],'left':leaf,'right':leaf}
        self.assertFalse(check_root(r['problem'],c))
        self.assertEqual(root(E.make({1:[1],0:[-1]}),F(0),F(1))['status'],'unknown_endpoints')

    def test_malformed_certificates(self):
        f=E.make({1:[1],0:[-1]})
        for bad in [None,[],{},'certificate',{'kind':'ladder'},{'kind':'ladder','cofactors':None}]:
            self.assertFalse(check_ladder(f.problem(),bad))

    def test_random_bfs_minimality(self):
        rng=random.Random(20260915)
        for _ in range(120):
            f=E.make({r:[rng.randint(-3,3) for _ in range(rng.randint(1,3))]
                      for r in (-1,0,1)})
            b=ladder_search(f);o=optimal_ladder(f)
            self.assertEqual(b['status']=='certificate',o['status']=='certificate')
            if o['status']=='certificate':
                self.assertEqual(len(b['certificate']['cofactors']),o['steps'])
                self.assertTrue(check_minimality(f.problem(),o['certificate'],o['minimality']))
            else:self.assertTrue(check_obstruction(f.problem(),o['certificate']))


if __name__=='__main__':unittest.main()
