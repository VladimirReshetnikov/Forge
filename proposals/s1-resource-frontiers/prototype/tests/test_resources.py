from __future__ import annotations
import copy
import json
from pathlib import Path
import subprocess
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from forge_resources import producer as P
from forge_resources.model import Net, ResourceSummary, RunDAG
from forge_resources.checker import (check_frontier, check_threshold, check_parameters,
    check_lasso, check_run, check_runs, load_json, InvalidCertificate, ResourceLimit, Limits)
from forge_resources.examples import *


class FrontierTests(unittest.TestCase):
    def setUp(self):
        self.p = copy.deepcopy(MUTEX)
        self.c = P.frontier(self.p)["certificate"]

    def test_mutex_frontier(self):
        self.assertEqual(check_frontier(self.p, self.c)["basis"],
                         [[0, 0, 2], [1, 1, 1], [2, 2, 0]])

    def test_broken_mutex_frontier(self):
        c = P.frontier(BROKEN_MUTEX)["certificate"]
        self.assertEqual(check_frontier(BROKEN_MUTEX, c)["basis"],
                         [[0, 0, 2], [1, 0, 1], [2, 0, 0]])

    def test_unbounded_safe(self):
        c = P.frontier(UNBOUNDED_SAFE)["certificate"]
        self.assertEqual(check_frontier(UNBOUNDED_SAFE, c)["basis"], [[2, 0]])

    def test_empty_targets(self):
        p = problem(1, [("grow", [0], [1])], [])
        c = P.frontier(p)["certificate"]
        self.assertEqual(check_frontier(p, c)["basis"], [])

    def test_empty_target_vector(self):
        p = problem(0, [], [[]])
        self.assertEqual(check_frontier(p, P.frontier(p)["certificate"])["basis"], [[]])

    def test_zero_dimension_empty_targets(self):
        p = problem(0, [], [])
        self.assertEqual(check_frontier(p, P.frontier(p)["certificate"])["basis"], [])

    def test_zero_target_dominates(self):
        p = problem(2, [], [[1, 1], [0, 0]])
        self.assertEqual(check_frontier(p, P.frontier(p)["certificate"])["basis"], [[0, 0]])

    def test_even_growth_is_coverability_not_exact_reachability(self):
        c = P.frontier(EVEN_GROWTH)["certificate"]
        self.assertEqual(check_frontier(EVEN_GROWTH, c)["basis"], [[0]])
        self.assertEqual(Net.from_dict(EVEN_GROWTH).transitions[0].fire((0,)), (2,))

    def test_duplicate_targets_are_harmless(self):
        p = problem(1, [], [[1], [1]])
        self.assertEqual(check_frontier(p, P.frontier(p)["certificate"])["basis"], [[1]])

    def test_budget_exhaustion_is_unknown(self):
        r = P.frontier(self.p, max_candidates=0)
        self.assertEqual(r["status"], "UNKNOWN"); self.assertIsNone(r["certificate"])

    def test_missing_closure(self):
        self.c["predecessor_cover"][0] = []
        with self.assertRaises(InvalidCertificate): check_frontier(self.p, self.c)

    def test_wrong_closure_orientation(self):
        self.c["predecessor_cover"][0][0] = 0
        with self.assertRaises(InvalidCertificate): check_frontier(self.p, self.c)

    def test_missing_target(self):
        self.c["target_cover"] = []
        with self.assertRaises(InvalidCertificate): check_frontier(self.p, self.c)

    def test_false_positive_run(self):
        self.c["basis"][-1]["run"] = 0
        with self.assertRaises(InvalidCertificate): check_frontier(self.p, self.c)

    def test_wrong_problem(self):
        p = copy.deepcopy(self.p); p["transitions"][0]["name"] += "_changed"
        with self.assertRaises(InvalidCertificate): check_frontier(p, self.c)

    def test_changed_target(self):
        p = copy.deepcopy(self.p); p["targets"] = [[0, 0, 3]]
        with self.assertRaises(InvalidCertificate): check_frontier(p, self.c)

    def test_boolean_not_integer(self):
        self.c["basis"][0]["marking"][0] = False
        with self.assertRaises(InvalidCertificate): check_frontier(self.p, self.c)

    def test_negative_vector(self):
        self.c["basis"][0]["marking"][0] = -1
        with self.assertRaises(InvalidCertificate): check_frontier(self.p, self.c)

    def test_dimension_mismatch(self):
        self.c["basis"][0]["marking"].append(0)
        with self.assertRaises(InvalidCertificate): check_frontier(self.p, self.c)

    def test_inhibitor_refused(self):
        self.p["transitions"][0]["inhibitor"] = [0]
        with self.assertRaises(ValueError): P.frontier(self.p)
        with self.assertRaises(InvalidCertificate): check_frontier(self.p, self.c)

    def test_reset_refused(self):
        self.p["transitions"][0]["reset"] = [0]
        with self.assertRaises(ValueError): P.frontier(self.p)

    def test_duplicate_transition_name(self):
        self.p["transitions"][1]["name"] = self.p["transitions"][0]["name"]
        with self.assertRaises(ValueError): P.frontier(self.p)

    def test_extra_fields_refused(self):
        self.c["accepted"] = True
        with self.assertRaises(InvalidCertificate): check_frontier(self.p, self.c)

    def test_unsorted_basis(self):
        self.c["basis"].reverse()
        with self.assertRaises(InvalidCertificate): check_frontier(self.p, self.c)

    def test_duplicate_basis(self):
        self.c["basis"].insert(0, copy.deepcopy(self.c["basis"][0]))
        with self.assertRaises(InvalidCertificate): check_frontier(self.p, self.c)

    def test_no_search_import(self):
        command = "import sys; from forge_resources.checker import check_frontier; " \
                  "assert 'forge_resources.producer' not in sys.modules; " \
                  "assert 'forge_resources.model' not in sys.modules"
        subprocess.run([sys.executable, "-S", "-c", command], check=True,
                       cwd=Path(__file__).resolve().parents[1])


class ParameterTests(unittest.TestCase):
    def test_mutex_all_populations(self):
        fc = P.frontier(MUTEX)["certificate"]
        c = P.threshold(MUTEX, fc, [1, 0, 0], [0, 1, 0])
        self.assertTrue(check_threshold(c["query"], c)["all_safe"])

    def test_bug_threshold_two(self):
        fc = P.frontier(BROKEN_MUTEX)["certificate"]
        c = P.threshold(BROKEN_MUTEX, fc, [1, 0, 0], [0, 1, 0])
        self.assertEqual(check_threshold(c["query"], c)["threshold"], 2)

    def test_wrong_threshold(self):
        fc = P.frontier(BROKEN_MUTEX)["certificate"]
        c = P.threshold(BROKEN_MUTEX, fc, [1, 0, 0], [0, 1, 0])
        c["threshold"] = 3
        with self.assertRaises(InvalidCertificate): check_threshold(c["query"], c)

    def test_nonminimal_basis_threshold(self):
        fc = P.frontier(BROKEN_MUTEX)["certificate"]
        c = P.threshold(BROKEN_MUTEX, fc, [1, 0, 0], [0, 1, 0])
        c["basis_thresholds"][-1] = 3
        with self.assertRaises(InvalidCertificate): check_threshold(c["query"], c)

    def test_negative_slope_refused(self):
        fc = P.frontier(MUTEX)["certificate"]
        with self.assertRaises(ValueError): P.threshold(MUTEX, fc, [-1, 0, 0], [3, 1, 0])

    def test_two_parameter_mutex(self):
        fc = P.frontier(MUTEX)["certificate"]
        c = P.parameters(MUTEX, fc, [[1, 0], [0, 1], [0, 0]], [0, 0, 0])["certificate"]
        self.assertEqual(check_parameters(c["query"], c)["minima"], [[2, 2]])

    def test_nonconvex_parameter_frontier(self):
        fc = P.frontier(NO_TRANSITIONS)["certificate"]
        c = P.parameters(NO_TRANSITIONS, fc, [[1, 0], [0, 1]], [0, 0])["certificate"]
        self.assertEqual(check_parameters(c["query"], c)["minima"], [[1, 2], [2, 1]])

    def test_wrong_safe_box_cell(self):
        fc = P.frontier(NO_TRANSITIONS)["certificate"]
        c = P.parameters(NO_TRANSITIONS, fc, [[1, 0], [0, 1]], [0, 0])["certificate"]
        c["covers"][-1] = -1
        with self.assertRaises(InvalidCertificate): check_parameters(c["query"], c)

    def test_too_small_cap(self):
        fc = P.frontier(NO_TRANSITIONS)["certificate"]
        c = P.parameters(NO_TRANSITIONS, fc, [[1, 0], [0, 1]], [0, 0])["certificate"]
        c["caps"][0] = 0
        with self.assertRaises(InvalidCertificate): check_parameters(c["query"], c)

    def test_parameter_budget_is_unknown(self):
        fc = P.frontier(NO_TRANSITIONS)["certificate"]
        self.assertEqual(P.parameters(NO_TRANSITIONS, fc, [[1, 0], [0, 1]], [0, 0], max_box=1)["status"], "UNKNOWN")

    def test_no_parameters(self):
        fc = P.frontier(NO_TRANSITIONS)["certificate"]
        c = P.parameters(NO_TRANSITIONS, fc, [[], []], [2, 2])["certificate"]
        self.assertEqual(check_parameters(c["query"], c)["minima"], [[]])


class RunTests(unittest.TestCase):
    def test_noncommutative_composition(self):
        t = Net.from_dict(problem(1, [("spend", [2], [0]), ("earn", [0], [2])], [])).transitions
        a, b = (ResourceSummary.step(x) for x in t)
        self.assertNotEqual(a.then(b), b.then(a))

    def test_huge_exact_run(self):
        n = 10 ** 100
        net = Net.from_dict(DEPLETION); dag = RunDAG(net)
        root = dag.repeat(dag.step(0), n)
        q = {"problem": DEPLETION, "initial": [n + 1, 0], "final": [1, n], "length": n}
        c = {"schema": "forge.resources.run.v1", "query": q, "runs": dag.nodes, "root": root}
        self.assertEqual(check_run(q, c)["represented_length"], n)
        self.assertEqual(len(dag.nodes), 3)

    def test_disabled_huge_run(self):
        n = 10 ** 20; net = Net.from_dict(DEPLETION); dag = RunDAG(net)
        root = dag.repeat(dag.step(0), n)
        q = {"problem": DEPLETION, "initial": [n, 0], "final": [0, n], "length": n}
        c = {"schema": "forge.resources.run.v1", "query": q, "runs": dag.nodes, "root": root}
        with self.assertRaises(InvalidCertificate): check_run(q, c)

    def test_negative_repeat(self):
        nodes = [{"op": "empty"}, {"op": "repeat", "body": 0, "count": -1}]
        with self.assertRaises(InvalidCertificate): check_runs(MUTEX, nodes)

    def test_future_reference(self):
        nodes = [{"op": "empty"}, {"op": "seq", "left": 1, "right": 0}]
        with self.assertRaises(InvalidCertificate): check_runs(MUTEX, nodes)

    def test_bad_node_opcode(self):
        with self.assertRaises(InvalidCertificate): check_runs(MUTEX, [{"op": "trusted"}])

    def test_intermediate_bit_budget(self):
        nodes = [{"op": "step", "transition": 0}, {"op": "repeat", "body": 0, "count": 1000}]
        with self.assertRaises(ResourceLimit): check_runs(DEPLETION, nodes, Limits(summary_bits=5))

    def test_duplicate_json_key(self):
        with self.assertRaises(InvalidCertificate): load_json('{"x": 1, "x": 2}')

    def test_nonfinite_json(self):
        with self.assertRaises(InvalidCertificate): load_json('{"x": NaN}')

    def test_growth_lasso(self):
        c = P.find_lasso(UNBOUNDED_SAFE, [1, 0], place=1)["certificate"]
        self.assertEqual(check_lasso(c["query"], c)["growth"], [0, 1])

    def test_stutter_nontermination_not_unboundedness(self):
        c = P.find_lasso(STUTTER, [1], claim="nontermination")["certificate"]
        check_lasso(c["query"], c)
        self.assertEqual(P.find_lasso(STUTTER, [1], claim="unbounded")["status"], "UNKNOWN")
        c["query"]["claim"] = "unbounded"; c["query"]["place"] = 0
        with self.assertRaises(InvalidCertificate): check_lasso(c["query"], c)

    def test_empty_loop_refused(self):
        c = P.find_lasso(STUTTER, [1], claim="nontermination")["certificate"]
        c["loop"] = 0
        with self.assertRaises(InvalidCertificate): check_lasso(c["query"], c)

    def test_consuming_loop_refused(self):
        q = {"problem": DEPLETION, "initial": [100, 0], "claim": "nontermination", "place": None}
        c = {"schema": "forge.resources.lasso.v1", "query": q,
             "runs": [{"op": "empty"}, {"op": "step", "transition": 0}], "prefix": 0, "loop": 1}
        with self.assertRaises(InvalidCertificate): check_lasso(q, c)



class BindingTests(unittest.TestCase):
    def test_embedded_query_boolean_not_integer(self):
        p = copy.deepcopy(BROKEN_MUTEX)
        c = P.threshold(p, P.frontier(p)["certificate"], [1, 0, 0], [0, 1, 0])
        query = copy.deepcopy(c["query"])
        c["query"]["slope"][0] = True
        with self.assertRaises(InvalidCertificate): check_threshold(query, c)

    def test_embedded_run_query_boolean_not_integer(self):
        p = copy.deepcopy(STUTTER)
        dag = RunDAG(Net.from_dict(p))
        root = dag.step(0)
        nodes, roots = dag.compact([root])
        q = {"problem": p, "initial": [1], "final": [1], "length": 1}
        c = {"schema": "forge.resources.run.v1", "query": copy.deepcopy(q),
             "runs": nodes, "root": roots[0]}
        c["query"]["length"] = True
        with self.assertRaises(InvalidCertificate): check_run(q, c)

class EquivalenceTests(unittest.TestCase):
    def compare(self, p, leftword, rightword):
        from forge_resources.checker import check_equivalence
        net = Net.from_dict(p)
        def program(word):
            dag = RunDAG(net); root = dag.word(word); nodes, roots = dag.compact([root])
            return {'nodes': nodes, 'root': roots[0]}
        q = {'problem': p, 'left': program(leftword), 'right': program(rightword)}
        c = P.compare_programs(q)
        check_equivalence(q, c)
        return q, c

    def test_same_program(self):
        self.assertEqual(self.compare(MUTEX, [0,1,0], [0,1,0])[1]['verdict'], 'equivalent')

    def test_independent_steps_commute(self):
        p = problem(2, [('x',[1,0],[0,0]), ('y',[0,1],[0,0])], [])
        self.assertEqual(self.compare(p, [0,1], [1,0])[1]['verdict'], 'equivalent')

    def test_equal_effect_different_enabling(self):
        p = problem(1, [('spend',[1],[0]), ('earn',[0],[1])], [])
        q,c = self.compare(p,[0,1],[1,0])
        self.assertEqual(c['verdict'], 'different'); self.assertEqual(c['separating_initial'], [0])

    def test_equal_enabling_different_effect(self):
        p = problem(1, [('one',[0],[1]), ('two',[0],[2])], [])
        self.assertEqual(self.compare(p,[0],[1])[1]['verdict'], 'different')

    def test_step_count_is_not_observed(self):
        p = problem(1, [('identity',[0],[0])], [])
        self.assertEqual(self.compare(p,[],[0,0])[1]['verdict'], 'equivalent')

    def test_false_positive_equivalence_rejected(self):
        from forge_resources.checker import check_equivalence
        q,c = self.compare(DEPLETION,[],[0]); c['verdict']='equivalent';c['separating_initial']=None
        with self.assertRaises(InvalidCertificate): check_equivalence(q,c)

    def test_false_separator_rejected(self):
        from forge_resources.checker import check_equivalence
        q,c = self.compare(STUTTER,[],[]);c['verdict']='different';c['separating_initial']=[0]
        with self.assertRaises(InvalidCertificate): check_equivalence(q,c)

    def test_original_program_binding_rejected(self):
        from forge_resources.checker import check_equivalence
        q,c = self.compare(MUTEX,[0],[0]);c=copy.deepcopy(c);c['query']['right']['root']=0
        with self.assertRaises(InvalidCertificate): check_equivalence(q,c)

class AccelerationTests(unittest.TestCase):
    def test_large_threshold_primitive_unknown_accelerated_checked(self):
        p=problem(1,[('grow',[0],[1])],[[10**100]])
        self.assertEqual(P.frontier(p,max_candidates=100)['status'],'UNKNOWN')
        c=P.frontier(p,max_candidates=100,accelerate=True)['certificate']
        self.assertEqual(check_frontier(p,c)['basis'],[[0]])

    def test_guard_survives_acceleration(self):
        p=problem(2,[('guarded_grow',[1,0],[1,1])],[[0,10**100]])
        c=P.frontier(p,accelerate=True)['certificate']
        self.assertEqual(check_frontier(p,c)['basis'],[[0,10**100],[1,0]])

    def test_zero_effect_no_false_growth(self):
        self.assertEqual(check_frontier(STUTTER,P.frontier(STUTTER,accelerate=True)['certificate'])['basis'],[[2]])

    def test_bad_already_holds_below_demand(self):
        p=problem(1,[('grow_above_guard',[10],[11])],[[3]])
        self.assertEqual(check_frontier(p,P.frontier(p,accelerate=True)['certificate'])['basis'],[[3]])

    def test_mixed_effect_falls_back(self):
        p=problem(2,[('transfer',[1,0],[0,1])],[[0,6]])
        c=P.frontier(p,accelerate=True)['certificate']
        self.assertEqual(len(check_frontier(p,c)['basis']),7)

    def test_original_target_and_primitive_closure_still_checked(self):
        p=problem(1,[('grow',[0],[1])],[[10**50]])
        c=P.frontier(p,accelerate=True)['certificate'];c['predecessor_cover']=[]
        with self.assertRaises(InvalidCertificate):check_frontier(p,c)

    def test_acceleration_count_mutation_rejected(self):
        p=problem(1,[('grow',[0],[1])],[[10**50]])
        c=P.frontier(p,accelerate=True)['certificate']
        for node in c['runs']:
            if node['op']=='repeat':node['count']-=1
        with self.assertRaises(InvalidCertificate):check_frontier(p,c)

    def test_acceleration_respects_zero_budget(self):
        self.assertEqual(P.frontier(UNBOUNDED_SAFE,max_candidates=0,accelerate=True)['status'],'UNKNOWN')


if __name__ == "__main__":
    unittest.main()
