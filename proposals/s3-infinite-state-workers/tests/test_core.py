from __future__ import annotations
from copy import deepcopy
from itertools import product
import pathlib,sys,unittest
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/'prototype'))
import antichain,checker,fixtures,mixed,nominal,oracles

class CertificateTests(unittest.TestCase):
    def test_predecessor_exhaustive(self):
        for a,z,b,x in product(range(5),repeat=4):
            lhs=x>=a and x-a+z>=b
            rhs=x>=antichain.predecessor((a,),(z,),(b,))[0]
            self.assertEqual(lhs,rhs)

    def test_initial_cones(self):
        for base,ray,b in product(range(4),repeat=3):
            f={'control':0,'base':[base],'rays':[[ray]]}
            w=antichain.initial_witness(f,(b,))
            found=any(base+n*ray>=b for n in range(5))
            self.assertEqual(w is not None,found)
            self.assertEqual(checker.separated(f,[[b]]),not found)

    def test_mutex_parametric(self):
        for bug in [False,True]:
            p=fixtures.mutex(bug);checker.validate_vass(p)
            c=antichain.solve(p)
            self.assertEqual(c['kind'],'unsafe' if bug else 'safe')
            self.assertTrue(checker.check_vass(p,c))

    def test_nonconvex_unbounded(self):
        p=fixtures.axes();c=antichain.solve(p)
        self.assertEqual(c['basis'],[[[1,1]]]);self.assertTrue(checker.check_vass(p,c))

    def test_enabling_not_delta_only(self):
        p=fixtures.enabling_trap();c=antichain.solve(p)
        self.assertEqual(c['basis'],[[[1]],[[0]]]);self.assertTrue(checker.check_vass(p,c))
        self.assertFalse(checker.check_vass(p,{'schema':1,'kind':'unsafe','initial':0,'parameters':[],'transitions':[0]}))

    def test_long_counterexample(self):
        p=fixtures.delayed(101);c=antichain.solve(p)
        self.assertEqual(len(c['transitions']),101);self.assertTrue(checker.check_vass(p,c))

    def test_counter_budget(self):
        p=fixtures.delayed(101);c=antichain.solve(p,max_admissions=4)
        self.assertEqual(c['kind'],'unknown');self.assertFalse(checker.check_vass(p,c))

    def test_deleted_antichain_nodes_preserve_history(self):
        # target 12: the backward chain repeatedly removes its previous active vector.
        p=fixtures.delayed(12);c=antichain.solve(p)
        self.assertEqual(c['stats']['peak_basis'],1);self.assertEqual(len(c['transitions']),12)
        self.assertTrue(checker.check_vass(p,c))

    def test_swapped_registers(self):
        a=fixtures.lru();b=fixtures.permute_registers(a,[1,0]);c=nominal.equivalence(a,b)
        self.assertEqual(c['kind'],'equivalent');self.assertTrue(checker.check_nominal(a,b,c))

    def test_fresh_name_counterexample(self):
        a,b=fixtures.lru(),fixtures.lru(True)
        self.assertTrue(oracles.finite_nominal(a,b,2)['equivalent'])
        c=nominal.equivalence(a,b)
        self.assertEqual(c['kind'],'different');self.assertEqual(len(c['word']),5)
        self.assertEqual(len({x[1] for x in c['word']}),3)
        self.assertTrue(checker.check_nominal(a,b,c))

    def test_atom_outputs(self):
        a=fixtures.lru(atom_output=True);b=fixtures.permute_registers(a,[1,0])
        c=nominal.equivalence(a,b);self.assertTrue(checker.check_nominal(a,b,c))
        b['rules'][-1]['output']=['atom',['reg',1]] # wrong after swapping
        c=nominal.equivalence(a,b);self.assertEqual(c['kind'],'different')
        self.assertTrue(checker.check_nominal(a,b,c))

    def test_constants_fixed(self):
        a=fixtures.constant_detector();b=deepcopy(a);b['rules'][0]['output']=['bool',False]
        c=nominal.equivalence(a,b)
        self.assertEqual(c['word'],[['request',0]]);self.assertTrue(checker.check_nominal(a,b,c))

    def test_joint_equality_signature(self):
        sig=checker.equality_signature
        self.assertNotEqual(sig((2,3),0),sig((2,2),0))
        self.assertEqual(sig((2,3),0),sig((79,6),0))
        self.assertNotEqual(sig((None,),0),sig((0,),0))
        self.assertNotEqual(sig((0,),1),sig((7,),1))

    def test_forged_incomplete_orbit_set(self):
        a=fixtures.lru();b=fixtures.permute_registers(a,[1,0]);c=nominal.equivalence(a,b)
        c['states']=c['states'][:1]
        self.assertFalse(checker.check_nominal(a,b,c))

    def test_nominal_budget(self):
        a=fixtures.lru();c=nominal.equivalence(a,a,max_states=1)
        self.assertEqual(c['kind'],'unknown');self.assertFalse(checker.check_nominal(a,a,c))

    def test_mixed_parametric(self):
        for bug in [False,True]:
            p=fixtures.owner_pool(bug);checker.validate_register_net(p);c=mixed.solve(p)
            self.assertEqual(c['kind'],'unsafe' if bug else 'safe');self.assertTrue(checker.check_mixed(p,c))
        self.assertEqual(c['parameters'],[2]);self.assertEqual(len(c['steps']),2)
        self.assertEqual(len({step[2] for step in c['steps']}),2)

    def test_safe_certificate_mutation(self):
        p=fixtures.mutex();c=antichain.solve(p);c['basis']=[[]]
        self.assertFalse(checker.check_vass(p,c))
        p=fixtures.axes();c=antichain.solve(p);c['basis']=[[[0,0]]]
        self.assertFalse(checker.check_vass(p,c))

    def test_expected_problem_binding(self):
        p=fixtures.mutex();c=antichain.solve(p)
        self.assertFalse(checker.check_vass(fixtures.mutex(True),c))
        p=fixtures.owner_pool();c=mixed.solve(p)
        self.assertFalse(checker.check_mixed(fixtures.owner_pool(True),c))

    def test_witness_mutation(self):
        p=fixtures.delayed(5);c=antichain.solve(p);c['transitions'].pop()
        self.assertFalse(checker.check_vass(p,c))
        a,b=fixtures.lru(),fixtures.lru(True);c=nominal.equivalence(a,b);c['word']=c['word'][:-1]
        self.assertFalse(checker.check_nominal(a,b,c))

    def test_bad_integer_and_dimension(self):
        p=fixtures.axes();c=antichain.solve(p)
        for bad in [True,-1,1.0,'1',None]:
            mutated=deepcopy(c);mutated['basis'][0][0][0]=bad
            self.assertFalse(checker.check_vass(p,mutated))
        c['basis'][0][0].pop();self.assertFalse(checker.check_vass(p,c))

    def test_unsupported_operations(self):
        m=fixtures.lru();m['rules'][0]['guard']=['less',['input'],['reg',0]]
        with self.assertRaises(checker.Invalid):checker.validate_machine(m)
        m=fixtures.owner_pool();m['bad'][0]['guard']=['eq',['input'],['reg',0]]
        with self.assertRaises(checker.Invalid):checker.validate_register_net(m)

    def test_json_boundary(self):
        for text in ['{"x":1,"x":2}','{"x":NaN}']:
            with self.assertRaises(checker.Invalid):checker.load_json(text)
        with self.assertRaises(checker.Invalid):checker.load_json('{}',1)

    def test_null_not_a_data_input(self):
        a,b=fixtures.lru(),fixtures.lru(True)
        self.assertFalse(checker.check_nominal(a,b,{'schema':1,'kind':'different','word':[['request',None]]}))

    def test_redundant_valid_basis_accepted(self):
        p=fixtures.axes();c=antichain.solve(p)
        c['basis'][0].extend([[1,1],[2,2],[3,1]])
        self.assertTrue(checker.check_vass(p,c))

    def test_backwards_closure_not_only_bad_inclusion(self):
        p=fixtures.delayed(5)
        c={'schema':1,'kind':'safe','basis':[[[5]]]}
        self.assertTrue(checker.covered(c['basis'][0],[5]))
        self.assertTrue(checker.separated(p['initials'][0],c['basis'][0]))
        self.assertFalse(checker.check_vass(p,c))

    def test_noncanonical_orbit_labels_accepted(self):
        a=fixtures.lru();b=fixtures.permute_registers(a,[1,0])
        c=nominal.equivalence(a,b)
        for state in c['states']:
            state[2]=[None if v is None else 100+19*v for v in state[2]]
        self.assertTrue(checker.check_nominal(a,b,c))

    def test_malformed_model_rejected(self):
        p=fixtures.owner_pool();c=mixed.solve(p);p['bad']=[None]
        self.assertFalse(checker.check_mixed(p,c))

if __name__=='__main__':unittest.main(verbosity=2)
