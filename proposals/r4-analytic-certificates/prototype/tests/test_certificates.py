import unittest
from copy import deepcopy
from fractions import Fraction as Q
from decimal import Decimal, localcontext
from itertools import permutations
from math import factorial
from random import Random
from forge_analytic.core import *
from forge_analytic.bounds import *
from forge_analytic.search import *
from forge_analytic.check import verify, verify_goal, checked_op


def initial_jet_oracle(a, factors):
    """Direct jet/characteristic-polynomial calculation, not repeated op()."""
    char = [Q(1)]
    for rho in factors:
        nxt = [Q(0)]*(len(char)+1)
        for j, c in enumerate(char):
            nxt[j] -= rho*c
            nxt[j+1] += c
        char = nxt
    jets = []
    for n in range(len(char)):
        jets.append(sum((c*Q(factorial(n), factorial(n-k))*r**(n-k)
                         for (r,k),c in a.items() if k <= n), Q(0)))
    return sum((c*v for c,v in zip(char,jets)), Q(0))


class ExactCoreTests(unittest.TestCase):
    def test_canonical_roundtrip(self):
        a = make((1,2,'3/2'),(0,0,2),(1,2,'-1/2'))
        self.assertEqual(a, decode(encode(a)))
        with self.assertRaises(ValueError): decode([['1',0,'1'],['1',0,'1']])
        for bad in [True, 0.5, '2/2', '01', Decimal(1)]:
            with self.assertRaises(ValueError): rat(bad)

    def test_product_and_reflection(self):
        a, b = make((1,1,2)), make((-1,2,3))
        self.assertEqual(mul(a,b), make((0,3,6)))
        self.assertEqual(reflect(reflect(a)), a)

    def test_independent_stencil_and_jets(self):
        rng = Random(901)
        for _ in range(200):
            a = make(*[(Q(rng.randrange(-6,7),2),rng.randrange(4),rng.randrange(-5,6)) for _ in range(8)])
            fs = [Q(rng.randrange(-6,7),2) for _ in range(6)]
            q = a
            for n,r in enumerate(fs):
                self.assertEqual(origin(q), initial_jet_oracle(a, fs[:n]))
                self.assertEqual(op(q,r), checked_op(q,r))
                q=op(q,r)

    def test_annihilator(self):
        rng = Random(902)
        for _ in range(100):
            a = make(*[(rng.randrange(-3,4),rng.randrange(4),rng.randrange(-5,6)) for _ in range(8)])
            q=a
            for r in spectrum(a): q=op(q,r)
            self.assertFalse(q)


class BoundsTests(unittest.TestCase):
    def test_exp_against_high_precision_decimal(self):
        # Diagnostic oracle, not the source of mathematical soundness.
        rng = Random(903)
        with localcontext() as ctx:
            ctx.prec=160
            for _ in range(200):
                z=Q(rng.randrange(-2048,2049),8)
                lo,hi=exp_bounds(z)
                actual=(Decimal(z.numerator)/Decimal(z.denominator)).exp()
                self.assertLessEqual(Decimal(lo.numerator)/Decimal(lo.denominator),actual)
                self.assertGreaterEqual(Decimal(hi.numerator)/Decimal(hi.denominator),actual)

    def test_refining_precision(self):
        for z in [Q(-1000),Q(-1,3),Q(7,3),Q(0)]:
            lo,hi=exp_bounds(z,64,24)
            ll,hh=exp_bounds(z,128,48)
            self.assertLessEqual(lo,ll)
            self.assertGreaterEqual(hi,hh)

    def test_range_budgets(self):
        for bits in [True,1,5000]:
            with self.assertRaises(ValueError): exp_bounds(1,bits)


class LadderTests(unittest.TestCase):
    def test_sorted_order_is_complete_among_permutations(self):
        rng=Random(904)
        for _ in range(90):
            # Two degree-one groups give at most 6 distinct orders.
            a=make(*[(r,k,rng.randrange(-3,4)) for r in [-1,2] for k in [0,1]])
            fs=spectrum(a)
            exists=any(ladder(a,factors=p) is not None for p in set(permutations(fs)))
            self.assertEqual(ladder(a) is not None,exists)

    def test_high_order_boundary_zero(self):
        for n in range(25):
            a=taylor_remainder(n)
            cert=ladder(a)
            self.assertTrue(verify(a,cert))
            p={'polynomial':encode(a),'goal':{'kind':'positive_open_ray','anchor':'0'}}
            self.assertTrue(verify_goal(p,cert))
            p['goal']['kind']='positive_closed_ray'
            self.assertFalse(verify_goal(p,cert))

    def test_both_rays_exp_tangent(self):
        a=taylor_remainder(1)
        self.assertTrue(verify(a,ladder(a)))
        b=reflect(a)
        self.assertTrue(verify(b,ladder(b)))

    def test_ghost_improvement_and_true_obstruction(self):
        for eps in [Q(1),Q(1,2),Q(1,4),Q(1,16)]:
            a=make((2,0,1),(1,0,-4),(0,0,4+eps))
            self.assertIsNone(ladder(a))
            cert=ghost_search(a,max_extra=96)
            self.assertIsNotNone(cert)
            self.assertTrue(verify(a,cert))
        a=make((2,0,1),(1,0,-4),(0,0,4))
        self.assertIsNone(ghost_search(a,max_extra=96))

    def test_source_anchor_and_strictness_binding(self):
        a=make((1,0,1),(0,0,-2))
        cert=ladder(a,anchor=1)
        self.assertTrue(verify(a,cert))
        p={'polynomial':encode(a),'goal':{'kind':'nonnegative_ray','anchor':'0'}}
        self.assertFalse(verify_goal(p,cert))
        p['goal']['anchor']='1'
        self.assertTrue(verify_goal(p,cert))
        cert=deepcopy(cert)
        cert['anchor']='0'
        self.assertFalse(verify_goal(p,cert))

    def test_ladder_mutations(self):
        a=taylor_remainder(4)
        cert=ladder(a)
        mutations=[]
        b=deepcopy(cert); b['steps'][0]['rho']='17'; mutations.append(b)
        b=deepcopy(cert); b['steps'][0]['lower']='1'; mutations.append(b)
        b=deepcopy(cert); b['steps'].pop(); mutations.append(b)
        b=deepcopy(cert); b['steps'][0]['polynomial'][0][2]='111'; mutations.append(b)
        b=deepcopy(cert); b['bits']=True; mutations.append(b)
        b=deepcopy(cert); b['steps'][0]['rho']=0.5; mutations.append(b)
        for b in mutations: self.assertFalse(verify(a,b))
        self.assertFalse(verify(add(a,make((0,0,-1))),cert))


class TailAndCoverTests(unittest.TestCase):
    def test_random_tail_certificates(self):
        rng=Random(905)
        for _ in range(300):
            a=make(*[(Q(rng.randrange(-8,9),3),rng.randrange(6),rng.randrange(-9,10)) for _ in range(8)])
            self.assertTrue(verify(a,tail(a)))
        self.assertTrue(verify({},tail({})))

    def test_wrong_sign_cutoff_and_degree_rejected(self):
        a=make((1,0,1),(0,5,-1000))
        c=tail(a)
        for mutation in ['sign','cutoff','order']:
            b=deepcopy(c)
            if mutation=='sign': b['sign']=-1
            if mutation=='cutoff': b['cutoff']='1'
            if mutation=='order': b['orders'][0][1]=0
            self.assertFalse(verify(a,b))

    def test_tails_are_not_global_proofs(self):
        a=make((1,0,1),(0,0,-100))
        p={'polynomial':encode(a),'goal':{'kind':'nonnegative_ray','anchor':'0'}}
        self.assertFalse(verify_goal(p,tail(a)))

    def test_interval_cover(self):
        a=make((2,0,1),(1,0,-4),(0,0,5))
        c=compact_cover(a,0,2,max_depth=12)
        self.assertEqual(c['kind'],'cover-v1')
        self.assertTrue(verify(a,c))
        b=deepcopy(c); b['domain']=['0','3']; self.assertFalse(verify(a,b))
        b=deepcopy(c); b['tree']['split']='0'; self.assertFalse(verify(a,b))

    def test_genuine_counterpoint(self):
        a=make((1,0,1),(0,0,-2))
        c=compact_cover(a,0,1)
        self.assertEqual(c['kind'],'counterpoint-v1')
        self.assertTrue(verify(a,c))
        b=deepcopy(c); b['counterpoint']='2'; self.assertFalse(verify(a,b))
        p={'polynomial':encode(a),'goal':{'kind':'nonnegative_interval','domain':['0','1']}}
        self.assertFalse(verify_goal(p,c))

if __name__=='__main__': unittest.main(verbosity=2)
