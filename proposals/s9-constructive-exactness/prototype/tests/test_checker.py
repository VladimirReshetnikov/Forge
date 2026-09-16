"""Small dependency-free tests, separate from the generated certificate suite."""
import unittest
from exactness.checker import *

class CheckerTests(unittest.TestCase):
    def test_rectangular_multiply(self):
        a=Mat(2,3,(1,2,3,4,5,6)); b=Mat(3,1,(2,0,-1))
        self.assertEqual(a@b,Mat(2,1,(-1,2)))
    def test_empty_shapes(self):
        self.assertEqual(zero(3,0)@zero(0,4),zero(3,4))
        self.assertEqual(eye(0),zero(0,0))
    def test_transpose(self):
        a=Mat(2,3,tuple(range(6)));self.assertEqual(a.transpose().transpose(),a)
    def test_bool(self):
        with self.assertRaises(Rejected):integer(True)
    def test_float(self):
        with self.assertRaises(Rejected):integer(1.0)
    def test_duplicate_keys(self):
        with self.assertRaises(Rejected):strict_loads('{"x":1,"x":2}')
    def test_nonfinite_json(self):
        with self.assertRaises(Rejected):strict_loads('{"x":NaN}')
    def test_shape(self):
        with self.assertRaises(Rejected):matrix(dict(rows=0,cols=3,data=[0]))
    def test_unexpected_key(self):
        with self.assertRaises(Rejected):matrix(dict(rows=0,cols=3,data=[],rank=0))
    def test_noninteger_domain(self):
        with self.assertRaises(Rejected):check(dict(kind='cycle',domain='Q'),{})
    def test_input_bit_cap(self):
        with self.assertRaises(Rejected):integer(1<<MAX_BITS)
    def test_graded_map(self):
        with self.assertRaises(Rejected):graded(eye(1),[0],[0],1)

if __name__=='__main__':unittest.main()
