from fractions import Fraction as Q
from copy import deepcopy
import unittest
from forge_ap.models import *
from forge_ap.search import solve_parity, solve_transport, solve_mdp, solve_simulation
from forge_ap.check import parity, transport, mdp, simulation

class RegressionTests(unittest.TestCase):
    def test_priority_seen_once_does_not_win(self):
        p=Arena((0,0),(2,1),((1,),(1,)))
        c=solve_parity(p);parity(p,c)
        self.assertEqual(c['regions'][1]['vertices'],[0,1])
    def test_infinite_good_cycle_needs_no_global_descent(self):
        p=Arena((0,1),(1,2),((1,),(0,)))
        c=solve_parity(p);parity(p,c)
        self.assertEqual(c['regions'][0]['vertices'],[0,1])
    def test_adversary_edge_may_not_be_dropped(self):
        p=Arena((1,0),(0,1),((0,1),(1,)))
        false=Arena((1,0),(0,1),((0,),(1,)))
        c=solve_parity(false)
        with self.assertRaises(Invalid):parity(p,c)
    def test_probability_mass_must_be_exact(self):
        with self.assertRaises(Invalid):Transport.read({"kind":"transport","mu":[[1,3]],
            "nu":[[1,1]],"relation":[[True]]})
    def test_dependent_coupling_beats_independent_product(self):
        p=Transport((Q(1,2),Q(1,2)),(Q(1,2),Q(1,2)),((True,False),(False,True)))
        c=solve_transport(p);self.assertEqual(transport(p,c),0)
        d=deepcopy(c);d['joint']=[[[1,4],[1,4]],[[1,4],[1,4]]]
        with self.assertRaises(Invalid):transport(p,d)
    def test_optimal_defect_has_positive_dual(self):
        p=Transport((Q(1,3),Q(2,3)),(Q(2,3),Q(1,3)),((True,True),(False,True)))
        c=solve_transport(p);self.assertEqual(transport(p,c),Q(1,3))
        d=deepcopy(c);d['hall_subset']=[]
        with self.assertRaises(Invalid):transport(p,d)
    def test_universal_not_existential_scheduler(self):
        p=MDP((((Q(1),Q(0)),(Q(0),Q(1))),((Q(0),Q(1)),)),(1,),0)
        c=solve_mdp(p);self.assertEqual(mdp(p,c),'nontermination')
    def test_geometric_retry_has_finite_mean_but_infinite_path(self):
        p=MDP((((Q(3,4),Q(1,4)),),((Q(0),Q(1)),)),(1,),0)
        c=solve_mdp(p);mdp(p,c);self.assertEqual(c['values'][0],[4,1])
    def test_unreachable_trap_is_not_a_refutation(self):
        p=MDP((((Q(0),Q(1),Q(0)),),((Q(0),Q(1),Q(0)),),((Q(0),Q(0),Q(1)),)),(1,),0)
        c=solve_mdp(p);self.assertEqual(mdp(p,c),'optimal_bound')
        bad={'outcome':'nontermination','trap':[2],'policy':[-1,-1,0],
             'path':[],'probability_lower':[1,1]}
        with self.assertRaises(Invalid):mdp(p,bad)
    def test_zero_potential_cannot_ignore_time_cost(self):
        p=MDP((((Q(0),Q(1)),),((Q(0),Q(1)),)),(1,),0)
        c=solve_mdp(p);c['values'][0]=[0,1]
        with self.assertRaises(Invalid):mdp(p,c)
    def test_responder_may_depend_on_challenger_action(self):
        actions=(((Q(1),Q(0)),(Q(0),Q(1))),)*2
        p=Simulation(actions,actions,((True,False),(False,True)))
        c=solve_simulation(p);self.assertEqual(simulation(p,c),{(0,0),(1,1)})
        self.assertEqual([m['right_action'] for m in c['matches']],[0,1,0,1])
    def test_simulation_negative_is_not_trace_inequality(self):
        # A format-scope regression: no "unequal_traces" certificate is admitted.
        actions=(((Q(1),),),)
        p=Simulation(actions,actions,((True,),));c=solve_simulation(p)
        c['unequal_traces']=True
        with self.assertRaises(Invalid):simulation(p,c)
    def test_terminal_semantics_cannot_be_silently_repaired(self):
        p=MDP((((Q(0),Q(1)),),((Q(1),Q(0)),)),(1,),0)
        with self.assertRaises(Invalid):MDP.read(p.obj())
    def test_strict_json_boundary(self):
        for text in ['{"x":1,"x":2}','[0.0]','[NaN]','[Infinity]']:
            with self.assertRaises(Invalid):load_json(text)
        with self.assertRaises(Invalid):rational([2,4])
        with self.assertRaises(Invalid):rational([True,1])
        with self.assertRaises(Invalid):rational([1,0])

if __name__=='__main__':unittest.main()
