import copy
import json
import random
import unittest
from fractions import Fraction as Q
from forgeq import search as s, checker as c
import oracles


class ForgeQTests(unittest.TestCase):
    def test_reach_geometric(self):
        p={'actions':[[['1/2','1/2']],[['0','1']]],'target':[1]}
        a=s.reachability(p)
        self.assertTrue(c.check('reach',p,a)); self.assertEqual(a['rank'],['2','0'])

    def test_spurious_fixed_point_rejected(self):
        p={'actions':[[['1','0']],[['0','1']]],'target':[1]}
        fake={'kind':'reach_max','value':['1','1'],'policy':[0,0],'dead':[],'rank':['99','0']}
        self.assertFalse(c.check('reach',p,fake))
        a=s.reachability(p)
        self.assertEqual(a['value'],['0','1']); self.assertTrue(c.check('reach',p,a))

    def test_target_normalization_required(self):
        p={'actions':[[['1/2','1/2']],[['1','0']]],'target':[1]}
        self.assertFalse(c.check('runtime',p,{'kind':'runtime_upper','potential':['2','0']}))

    def test_scheduler_polarity(self):
        p={'actions':[[['1','0'],['0','1']],[['0','1']]],'target':[1]}
        self.assertTrue(c.check('reach',p,s.reachability(p)))
        self.assertEqual(s.runtime(p)['kind'],'unknown')
        self.assertFalse(c.check('runtime',p,{'kind':'runtime_upper','potential':['1','0']}))

    def test_reach_vertex_oracle(self):
        rng=random.Random(419)
        for _ in range(12):
            rows=[]
            for i in range(3):
                choices=[]
                for _ in range(2):
                    weights=[rng.randrange(4) for _ in range(4)]
                    if not sum(weights): weights[-1]=1
                    choices.append([Q(x,sum(weights)) for x in weights])
                rows.append(choices)
            rows.append([[Q(0),Q(0),Q(0),Q(1)]])
            p=s.dump({'actions':rows,'target':[3]})
            a=s.reachability(p)
            self.assertTrue(c.check('reach',p,a))
            self.assertEqual(list(map(Q,a['value'])),oracles.reach_vertices(p))

    def test_runtime_bound(self):
        p={'actions':[[['1/2','1/2'],['3/4','1/4']],[['0','1']]],'target':[1]}
        a=s.runtime(p)
        self.assertEqual(a['potential'],['4','0']);self.assertTrue(c.check('runtime',p,a))

    def test_transport_optimality(self):
        p=s.transport_problem(['1/2','1/2'],['1/3','2/3'],cost=[['0','1'],['1','0']])
        a=s.transport(p)
        self.assertTrue(c.check('transport',p,a))
        self.assertEqual(Q(a['joint'][0][1])+Q(a['joint'][1][0]),Q(1,6))

    def test_hall_cut(self):
        p=s.transport_problem(['3/4','1/4'],['1/4','3/4'],[(0,0),(1,1)])
        a=s.transport(p);self.assertEqual(a['kind'],'hall')
        self.assertTrue(c.check('transport',p,a))
        a['neighbors']=[];self.assertFalse(c.check('transport',p,a))

    def test_exact_small_residual(self):
        p=s.transport_problem(['1/2','1/2'],['1/2','1/2'])
        a=s.transport(p);a['joint'][0][0]=str(Q(a['joint'][0][0])+Q(1,10**30))
        self.assertFalse(c.check('transport',p,a))

    def test_marginals_not_optional(self):
        p=s.transport_problem(['1/2','1/2'],['1/2','1/2'])
        a=s.transport(p);a['joint']=[['0','0'],['0','0']]
        self.assertFalse(c.check('transport',p,a))

    def test_transport_independent_oracle(self):
        rng=random.Random(23)
        for _ in range(40):
            left=[0]*3;right=[0]*3
            for _ in range(5):
                left[rng.randrange(3)]+=1;right[rng.randrange(3)]+=1
            allowed={(i,j) for i in range(3) for j in range(3) if rng.random()<0.8}
            costs=[[rng.randrange(6) for _ in range(3)] for _ in range(3)]
            p=s.transport_problem([Q(x,5) for x in left],[Q(x,5) for x in right],allowed,costs)
            a=s.transport(p); self.assertTrue(c.check('transport',p,a))
            exact=oracles.integer_transport(left,right,costs,allowed)
            if exact is None: self.assertEqual(a['kind'],'hall')
            else:
                got=sum(Q(a['joint'][i][j])*costs[i][j] for i in range(3) for j in range(3))
                self.assertEqual(got,exact)

    def test_bisimulation_identity(self):
        p={'left':[['1/2','1/2'],['0','1']], 'right':[['1/2','1/2'],['0','1']],
           'obs_left':[0,1],'obs_right':[0,1],'start':[0,0]}
        a=s.bisimulation(p)
        self.assertTrue(c.check('bisimulation',p,a));self.assertEqual(a['kind'],'bisimulation')

    def test_trace_equivalent_not_bisimilar(self):
        p={'left':[['0','1/2','1/2','0','0'],['0','0','0','1','0'],
                   ['0','0','0','0','1'],['0','0','0','1','0'],['0','0','0','0','1']],
           'right':[['0','1','0','0'],['0','0','1/2','1/2'],['0','0','1','0'],['0','0','0','1']],
           'obs_left':[0,1,1,2,3],'obs_right':[0,1,2,3],'start':[0,0]}
        a=s.bisimulation(p)
        self.assertEqual(a['kind'],'no_bisimulation'); self.assertTrue(c.check('bisimulation',p,a))
        self.assertIn('NOT_trace',c.audit('bisimulation',p,a)['claim'])
        self.assertFalse(oracles.bisim_partition(p))
        for length in range(1,11):
            self.assertEqual(oracles.trace_law(p['left'],p['obs_left'],0,length),
                             oracles.trace_law(p['right'],p['obs_right'],0,length))

    def test_empty_negative_proof_rejected(self):
        p={'left':[['1']], 'right':[['1']], 'obs_left':[0], 'obs_right':[0], 'start':[0,0]}
        self.assertFalse(c.check('bisimulation',p,{'kind':'no_bisimulation','removals':[]}))

    def test_contraction(self):
        p={'left':[['3/4','1/4'],['1/4','3/4']], 'right':[['3/4','1/4'],['1/4','3/4']],
           'distance':[['0','1'],['1','0']], 'rate':'1/2','error':'0'}
        a=s.contraction(p);self.assertTrue(c.check('contraction',p,a))
        p['rate']='1/3';a=s.contraction(p)
        self.assertEqual(a['kind'],'rate_obstruction');self.assertTrue(c.check('contraction',p,a))

    def test_invalid_metric_rejected(self):
        p={'left':[['1','0'],['0','1']], 'right':[['1','0'],['0','1']],
           'distance':[['0','0'],['0','0']], 'rate':'1/2','error':'0'}
        self.assertFalse(c.check('contraction',p,s.contraction(p)))

    def test_poisson_polynomial(self):
        p={'jumps':[-1,1],'probabilities':['2/3','1/3'],'cost':['0','1']}
        a=s.polynomial_cost(p)
        self.assertEqual(a['potential'],['0','9/2','3/2'])
        self.assertTrue(c.check('polynomial_cost',p,a))
        self.assertTrue(oracles.stopped_cost_check(p,a))

    def test_symmetric_walk_is_unknown(self):
        p={'jumps':[-1,1],'probabilities':['1/2','1/2'],'cost':['1']}
        self.assertEqual(s.polynomial_cost(p)['kind'],'unknown')

    def test_zero_cost_does_not_prove_termination(self):
        p={'jumps':[0],'probabilities':['1'],'cost':['0']}
        a={'kind':'polynomial_cost','potential':['0'],'epsilon':'0'}
        self.assertTrue(c.check('polynomial_cost',p,a))
        self.assertIn('NOT_a_termination',c.audit('polynomial_cost',p,a)['claim'])

    def test_unsafe_natural_jump_rejected(self):
        p={'jumps':[-2,1],'probabilities':['2/3','1/3'],'cost':['1']}
        self.assertFalse(c.check('polynomial_cost',p,s.polynomial_cost(p)))

    def test_strict_decoder(self):
        for text in ['{"a":1,"a":2}','{"a":0.5}','{"a":NaN}']:
            with self.assertRaises(ValueError): c.loads(text)
        for x in [True,0.5,'1/0','1/2 ','2/4','1e-20']:
            with self.assertRaises((ValueError,ZeroDivisionError)): c.number(x)

    def test_search_budget_unknown(self):
        p={'actions':[[['1/2','1/2']],[['0','1']]],'target':[1]}
        self.assertEqual(s.reachability(p,max_policies=0)['kind'],'unknown')
        p=s.transport_problem(['1'],['1'])
        self.assertEqual(s.transport(p,max_augmentations=0)['kind'],'unknown')

    def test_source_substitution_rejected(self):
        p=s.transport_problem(['1/2','1/2'],['1/2','1/2'])
        a=s.transport(p)
        p['left']=['1/3','2/3'];self.assertFalse(c.check('transport',p,a))

    def test_checker_has_no_producer_import(self):
        import pathlib
        text=pathlib.Path(c.__file__).read_text()
        self.assertNotIn('import search',text)
        self.assertNotIn('from .search',text)


if __name__=='__main__':
    unittest.main(verbosity=2)
