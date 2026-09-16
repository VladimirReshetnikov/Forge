"""Small standard-library regression suite; run from prototype with unittest."""
import copy
import json
import tempfile
from pathlib import Path
import unittest
from forge_symmetry import producer as p
from forge_symmetry import checker as c

class SymmetryTests(unittest.TestCase):
    def checked(self, family='D', n=5):
        problem = p.named_problem(family, n)
        search = p.build_chain(problem)
        return problem, search, c.verify_chain(problem, search.export())

    def test_noncommuting_composition(self):
        a, b = (1, 0, 2), (0, 2, 1)
        self.assertEqual(p.mul(a, b), (1, 2, 0))
        self.assertNotEqual(p.mul(a, b), p.mul(b, a))
        self.assertEqual(p.action(p.mul(a, b), (10, 20, 30)), (30, 10, 20))

    def test_empty_action(self):
        problem, search, checked = self.checked('S', 0)
        self.assertEqual(checked.order, 1)
        self.assertTrue(checked.contains([]))
        inventory = c.verify_burnside(checked, p.burnside_certificate(problem))
        self.assertEqual(inventory.count_colors(0), 1)
        self.assertEqual(inventory.count_binary_weight(0), 1)
        cert, _ = p.canonical_certificate(search, [])
        self.assertEqual(c.verify_canonical(checked, [], cert)['best'], [])

    def test_membership_and_normal_forms(self):
        problem, _, checked = self.checked()
        self.assertEqual(set(checked.normal_forms()), set(p.enumerate_bfs(problem)))
        self.assertEqual(checked.order, 10)
        self.assertFalse(checked.contains([1,0,2,3,4]))

    def test_incomplete_chain_rejected_after_correct_order_product(self):
        # Every listed orbit is closed, all original generators are present,
        # and the order product is correct FOR THESE TABLES. Schreier closure fails.
        problem = {'degree': 3, 'generators': [[1,2,0], [1,0,2]]}
        partial = {'format':'forge.symmetry.chain.v1',
                   'word_dag':[['id'],['gen',0],['gen',1]], 'strong':[1,2],
                   'levels':[[[0,None,None],[1,0,1],[2,1,1]],
                             [[1,None,None]], [[2,None,None]]], 'order':3}
        with self.assertRaisesRegex(c.InvalidCertificate, 'Schreier generator'):
            c.verify_chain(problem, partial)

    def test_missing_orbit_with_recomputed_product(self):
        problem, search, _ = self.checked('C', 5)
        cert = search.export()
        cert['levels'][0].pop()
        cert['order'] = 4
        with self.assertRaisesRegex(c.InvalidCertificate, 'orbit is not closed'):
            c.verify_chain(problem, cert)

    def test_boolean_not_integer(self):
        problem, search, _ = self.checked()
        cert = search.export()
        cert['levels'][0][0][0] = False
        with self.assertRaises(c.InvalidCertificate):
            c.verify_chain(problem, cert)

    def test_json_controls(self):
        for text in ['{"degree":1,"degree":2}', '{"degree":1.0}', '{"degree":NaN}']:
            with tempfile.TemporaryDirectory() as temp:
                target = Path(temp)/'bad.json'
                target.write_text(text)
                with self.assertRaises(c.InvalidCertificate):
                    c.load_json(target)

    def test_canonical_cover(self):
        problem, search, checked = self.checked()
        colors = [2,0,1,0,2]
        cert, _ = p.canonical_certificate(search, colors)
        result = c.verify_canonical(checked, colors, cert)
        exact = min(p.action(g, tuple(colors)) for g in p.enumerate_bfs(problem))
        self.assertEqual(tuple(result['best']), exact)
        corrupt = copy.deepcopy(cert)
        if corrupt['cover'][0] == 'split':
            corrupt['cover'][1].pop()
            with self.assertRaises(c.InvalidCertificate):
                c.verify_canonical(checked, colors, corrupt)

    def test_alternating_parity_cases(self):
        _, search, checked = self.checked('A', 5)
        for colors in [[1,0,2,3,4], [1,0,0,2,3], [4,3,2,1,0]]:
            cert = p.canonical_family_certificate(search, colors, 'A')
            result = c.verify_canonical_family(checked, colors, cert)
            brute = min(p.action(g, tuple(colors)) for g in checked.normal_forms())
            self.assertEqual(tuple(result['best']), brute)
        cert = p.canonical_family_certificate(search, [1,0,2,3,4], 'A')
        self.assertEqual(cert['best'], [0,1,2,4,3])

    def test_burnside_D10(self):
        problem, _, checked = self.checked('D',10)
        inv = c.verify_burnside(checked, p.burnside_certificate(problem))
        self.assertEqual(inv.polynomial_numerator(), [[1,4],[2,4],[5,6],[6,5],[10,1]])
        self.assertEqual(inv.count_colors(2), 78)
        self.assertEqual(inv.count_binary_weight(5), 16)

    def test_semantic_gate(self):
        _, _, checked = self.checked('D',5)
        clauses = [[i+1, (i+1)%5+1] for i in range(5)]
        self.assertTrue(c.verify_cnf_symmetry(checked, clauses, [1]*5))
        with self.assertRaises(c.InvalidCertificate):
            c.verify_cnf_symmetry(checked, clauses, [2,1,1,1,1])
        with self.assertRaises(c.InvalidCertificate):
            c.verify_cnf_symmetry(checked, clauses+[[1]])

    def test_budget_is_distinct_from_rejection(self):
        problem, search, _ = self.checked()
        with self.assertRaises(c.CheckLimit):
            c.verify_chain(problem, search.export(), max_checks=0)
        with self.assertRaises(p.SearchLimit):
            p.build_chain(problem, max_steps=0)

if __name__ == '__main__':
    unittest.main()
