"""Named regressions and deliberate, invalid certificate mutations."""
from __future__ import annotations
import copy, json, sys, unittest
from pathlib import Path
from dataclasses import replace
from fractions import Fraction as F
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'prototype'))
from forge_horizon.models import PDS,Rule,Game,Chain,Invalid
from forge_horizon import pushdown,games,markov
from forge_horizon.checkers import check_pds,check_game,check_chain
from forge_horizon.codec import dumps,loads,pack_model,unpack_model
from oracles import game_oracle,pds_bfs

class PushdownTests(unittest.TestCase):
    def setUp(self):
        self.p=PDS(1,3,(Rule(0,0,0,()),Rule(0,1,0,(0,0)),Rule(0,2,0,(1,1))),0,(2,),frozenset({0}))
    def test_dag_is_compressed(self):
        ans=check_pds(self.p,pushdown.solve(self.p));self.assertEqual(ans['dag_nodes'],3)
        self.assertEqual(ans['expanded_steps'],7)
    def test_circular_positive_rejected(self):
        p=PDS(1,1,(Rule(0,0,0,(0,)),),0,(0,),frozenset({0}))
        c={'kind':'pds_reach','nodes':[{'triple':[0,0,0],'rule':0,'children':[0]}],'chain':[0]}
        with self.assertRaises(Invalid):check_pds(p,c)
    def test_missing_base_rejected(self):
        p=replace(self.p,finals=frozenset())
        c=pushdown.solve(p);c['relation'].remove([0,0,0])
        with self.assertRaises(Invalid):check_pds(p,c)
    def test_missing_binary_consequence_rejected(self):
        p=replace(self.p,finals=frozenset())
        c=pushdown.solve(p);c['relation'].remove([0,2,0])
        with self.assertRaises(Invalid):check_pds(p,c)
    def test_wrong_target_rejected(self):
        c=pushdown.solve(self.p)
        with self.assertRaises(Invalid):check_pds(replace(self.p,finals=frozenset()),c)
    def test_false_infinite_stack_negative_detected(self):
        p=PDS(2,1,(Rule(0,0,0,(0,0)),Rule(0,0,0,())),0,(0,),frozenset({1}))
        self.assertEqual(check_pds(p,pushdown.solve(p))['outcome'],'unreachable')
        found,complete,_=pds_bfs(p,8);self.assertFalse(found);self.assertFalse(complete)
    def test_empty_stack_and_monitor(self):
        p=PDS(1,1,(),0,(),frozenset({0}))
        self.assertEqual(check_pds(p,pushdown.solve(p))['expanded_steps'],0)
        c=pushdown.compile_regular_target(p,((0,),),(0,),frozenset({0}))
        self.assertEqual(check_pds(c,pushdown.solve(c))['outcome'],'reachable')
    def test_top_first_monitor_orientation(self):
        # DFA recognizes exactly 01 (and no other word).
        delta=((1,3),(3,2),(3,3),(3,3))
        for word,expected in (((0,1),'reachable'),((1,0),'unreachable')):
            p=PDS(1,2,(),0,word,frozenset())
            compiled=pushdown.compile_regular_target(p,delta,(0,),frozenset({2}))
            self.assertEqual(check_pds(compiled,pushdown.solve(compiled))['outcome'],expected)
    def test_duplicate_summary_rejected(self):
        p=replace(self.p,finals=frozenset());c=pushdown.solve(p);c['relation'].append(c['relation'][0])
        with self.assertRaises(Invalid):check_pds(p,c)
    def test_illegal_symbol_rejected(self):
        with self.assertRaises(Invalid):pushdown.solve(replace(self.p,stack=(3,)))

class GameTests(unittest.TestCase):
    def test_owner_changes_answer(self):
        # Protagonist can exit; antagonist can remain in the nonaccepting loop.
        edges=((0,1),(1,))
        w=Game((0,0),edges,frozenset({1}));l=replace(w,owner=(1,0))
        self.assertIn(0,games.solve(w)['winning']['region'])
        self.assertIn(0,games.solve(l)['losing']['region'])
    def test_changed_owner_rejects_policy(self):
        g=Game((0,0),((0,1),(1,)),frozenset({1}));c=games.solve(g)['winning']
        with self.assertRaises(Invalid):check_game(replace(g,owner=(1,0)),c,0)
    def test_reachability_is_not_buchi(self):
        g=Game((0,0),((1,),(1,)),frozenset({0}))
        self.assertEqual(check_game(g,games.solve(g)['losing'],0)['outcome'],'losing')
    def test_rank_reset_at_acceptance(self):
        g=Game((0,1),((1,),(0,)),frozenset({0}));c=games.solve(g)['winning']
        self.assertEqual(check_game(g,c,0)['outcome'],'winning')
        self.assertLess(c['rank'][0],c['rank'][1])
    def test_spurious_nonaccepting_selfloop_rejected(self):
        g=Game((0,),((0,),),frozenset())
        c={'kind':'buchi_win','region':[0],'rank':[0],'policy':[0]}
        with self.assertRaises(Invalid):check_game(g,c,0)
    def test_spurious_accepting_negative_rejected(self):
        g=Game((1,),((0,),),frozenset({0}))
        c={'kind':'buchi_lose','region':[0],'rank':[1],'policy':[0]}
        with self.assertRaises(Invalid):check_game(g,c,0)
    def test_deadlock_is_not_silently_totalized(self):
        with self.assertRaises(Invalid):games.solve(Game((0,),((),),frozenset()))
    def test_opponent_cannot_be_omitted(self):
        g=Game((1,0),((0,1),(1,)),frozenset({1}))
        c={'kind':'buchi_win','region':[0,1],'rank':[1,0],'policy':[None,1]}
        with self.assertRaises(Invalid):check_game(g,c,0)
    def test_negative_rank_mutation(self):
        g=Game((0,0),((1,),(1,)),frozenset({0}));c=games.solve(g)['losing']
        c['rank'][0]=0
        with self.assertRaises(Invalid):check_game(g,c,0)

class MarkovTests(unittest.TestCase):
    def setUp(self):
        self.c=Chain(((F(3,4),F(1,4)),(F(0),F(1))),frozenset({1}),
                     (F(0),F(1)),(F(3,2),F(0)))
    def test_geometric_exact_values(self):
        a=check_chain(self.c,markov.solve(self.c))
        self.assertEqual((a['expected_time'],a['expected_cost'],a['expected_terminal_payoff']),(4,6,1))
    def test_cyclic_harmonic_only_not_proof(self):
        c=Chain(((F(1),),),frozenset(),(F(0),),(F(1),))
        fake={'kind':'mc_absorb','support':[0],'time':[F(0)],'cost':[F(0)],'value':[F(1,2)]}
        with self.assertRaises(Invalid):check_chain(c,fake)
    def test_changed_probability_rejected(self):
        proof=markov.solve(self.c)
        changed=replace(self.c,matrix=((F(1,2),F(1,2)),(F(0),F(1))))
        with self.assertRaises(Invalid):check_chain(changed,proof)
    def test_omit_positive_probability_successor(self):
        proof=markov.solve(self.c);proof['support']=[0]
        proof['time'][1]=proof['cost'][1]=proof['value'][1]=None
        with self.assertRaises(Invalid):check_chain(self.c,proof)
    def test_unreachable_trap_does_not_invalidate_start(self):
        c=Chain(((F(0),F(1),F(0)),(F(0),F(1),F(0)),(F(0),F(0),F(1))),
                frozenset({1}),(F(0),F(1),F(0)),(F(1),F(0),F(1)))
        self.assertEqual(check_chain(c,markov.solve(c))['outcome'],'almost_sure')
    def test_trap_needs_positive_path(self):
        c=Chain(((F(0),F(1),F(0)),(F(0),F(1),F(0)),(F(0),F(0),F(1))),
                frozenset({1}),(F(0),F(1),F(0)),(F(1),F(0),F(1)))
        proof={'kind':'mc_trap','closed':[2],'path':[0,2]}
        with self.assertRaises(Invalid):check_chain(c,proof)
    def test_normalization_rejected(self):
        bad=replace(self.c,matrix=((F(3,4),F(1,2)),(F(0),F(1))))
        with self.assertRaises(Invalid):markov.solve(bad)
    def test_floats_rejected(self):
        bad=replace(self.c,matrix=((0.75,0.25),(F(0),F(1))))
        with self.assertRaises(Invalid):markov.solve(bad)
    def test_each_numeric_vector_mutation_rejected(self):
        for name in ('time','cost','value'):
            proof=markov.solve(self.c);proof[name][0]+=F(1,7)
            with self.assertRaises(Invalid):check_chain(self.c,proof)
    def test_fractional_payoff_is_expectation_not_event(self):
        c=replace(self.c,payoff=(F(0),F(1,3)))
        ans=check_chain(c,markov.solve(c))
        self.assertEqual(ans['expected_terminal_payoff'],F(1,3))
        self.assertNotIn('success_probability',ans)
    def test_all_terminal_start(self):
        c=replace(self.c,start=1)
        a=check_chain(c,markov.solve(c));self.assertEqual(a['expected_time'],0)
    def test_no_terminal(self):
        c=Chain(((F(1),),),frozenset(),(F(0),),(F(1),))
        a=check_chain(c,markov.solve(c));self.assertEqual(a['failure_probability_lower_bound'],1)
    def test_trap_contains_no_terminal(self):
        bad={'kind':'mc_trap','closed':[1],'path':[0,1]}
        with self.assertRaises(Invalid):check_chain(self.c,bad)

class TransportTests(unittest.TestCase):
    def test_roundtrip_fraction(self):
        x={'value':F(-5,13),'nested':[F(2,7),None]};self.assertEqual(loads(dumps(x)),x)
    def test_duplicate_json_keys_rejected(self):
        with self.assertRaises(Invalid):loads('{"kind":"x","kind":"y"}')
    def test_zero_denominator_rejected(self):
        with self.assertRaises(Invalid):loads('{"rational":[1,0]}')
    def test_bool_not_a_state(self):
        with self.assertRaises(Invalid):games.solve(Game((True,),((0,),),frozenset()))

if __name__=='__main__':unittest.main(verbosity=2)
