"""Small API controls, distinct from the generated experiment corpus."""
import unittest
from formula import eq, Exists, least_graph, rename_free, free_variables
from producer import Compiler, extract_witness
from checker import verify, check_witness, Rejected

class Interfaces(unittest.TestCase):
    def test_least_requires_fresh_variable(self):
        with self.assertRaises(ValueError):
            least_graph(eq({'y': 1, 'u': -1}), 'y', 'u')

    def test_least_rejects_bound_capture(self):
        with self.assertRaises(ValueError):
            least_graph(Exists('u', eq({'y': 1, 'u': -1})), 'y', 'u')

    def test_capture_avoiding_rename(self):
        with self.assertRaises(ValueError):
            rename_free(Exists('z', eq({'y': 1, 'z': -1})), 'y', 'z')

    def test_free_names(self):
        self.assertEqual(free_variables(Exists('z', eq({'y': 1, 'z': -1}))), {'y'})

    def test_zero_needs_hidden_tail(self):
        query = {'context': [], 'formula': Exists('y', eq({'y': 1}, 1))}
        c = Compiler().bundle(query['formula'], query['context'])
        self.assertEqual(verify(c, query)['verdict'], 'valid')

    def test_least_large_witness(self):
        q = {'context': ['x', 'y'], 'formula': least_graph(eq({'y': 1, 'x': -2}, 1), 'y', 'z')}
        c = Compiler().bundle(q['formula'], q['context'])
        verify(c, q)
        d = c['nodes'][c['root']]['dfa']
        inputs = [2**200 + 17]
        r = extract_witness(d, inputs)
        self.assertIsNotNone(r)
        check_witness(d, inputs, r)
        self.assertEqual(r['witness'], 2 * inputs[0] + 1)

    def test_original_query_required(self):
        q = {'context': ['x'], 'formula': eq({'x': 1}, 0)}
        c = Compiler().bundle(q['formula'], q['context'])
        wrong = {'context': ['x'], 'formula': eq({'x': 1}, 1)}
        with self.assertRaises(Rejected):
            verify(c, wrong)

if __name__ == '__main__':
    unittest.main(verbosity=2)
