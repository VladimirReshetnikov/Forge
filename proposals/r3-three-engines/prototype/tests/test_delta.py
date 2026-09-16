import copy,json,unittest
from fractions import Fraction as F
from pathlib import Path
from forge_delta import poly_search as ps,poly_check as pc,nc_search as ns,nc_check as nc
from forge_delta import analytic_search as an,analytic_check as ac
from forge_delta import poly_witness as pw
from run_experiments import corner

class DeltaTests(unittest.TestCase):
    def test_corner_affine_obstruction(self):
        p=corner();c=ps.prove(p);self.assertTrue(pc.check(p,c))
        dag=pw.compile_witness(p,c)
        values=[pw.evaluate(dag,x)[0] for x in [(0,0),(1,0),(0,1),(1,1)]]
        self.assertEqual(values,[F(0),F(0),F(0),F(1)])
        self.assertNotEqual(values[0]+values[3],values[1]+values[2])
    def test_projection_pair_coverage_is_required(self):
        p=corner();c=ps.prove(p)
        c['steps'][0]['required']=[]
        self.assertFalse(pc.check(p,c))
    def test_strict_zero_is_a_contradiction(self):
        p={'parameters':0,'variables':1,'domain':[],'target':[ps.row([1,0],True),ps.row([-1,0])]}
        c=ps.prove(p);self.assertEqual(c['kind'],'refuted');self.assertTrue(pc.check(p,c))
    def test_zero_weight_does_not_carry_strictness(self):
        self.assertFalse(pc.contradiction([((F(0),F(1)),True)],['0'],1))
    def test_invalid_program_cannot_be_compiled(self):
        p=corner();c=ps.prove(p);c['witness_rule']='unchecked-source'
        with self.assertRaises(ValueError):pw.compile_witness(p,c)
    def test_noncommutative_critical_pair(self):
        rel=[{(0,1):F(1),(0,):F(-1)},{(1,0):F(1),(1,):F(-1)}]
        p={'generators':2,'relations':list(map(ns.wire,rel)),'target':ns.wire({(0,0):F(1),(0,):F(-1)})}
        self.assertEqual(ns.prove(p,complete=False)['kind'],'unknown')
        self.assertTrue(nc.check(p,ns.prove(p)))
    def test_nc_contexts_do_not_commute(self):
        p={'generators':2,'relations':[ns.wire({(0,1):F(1),(0,):F(-1)})],
           'target':ns.wire({(1,0,1):F(1),(1,0):F(-1)})}
        c={'kind':'proved','terms':[{'left':[1],'relation':0,'right':[],'coefficient':'1'}]}
        self.assertTrue(nc.check(p,c));c['terms'][0].update(left=[],right=[1]);self.assertFalse(nc.check(p,c))
    def test_exp_jet(self):
        p={'expr':an.sub(an.sub(an.op('exp',an.X),an.C(1)),an.X),'box':['-1','1']}
        self.assertTrue(ac.check(p,an.prove(p,jet_order=2)))
    def test_odd_jet_left_domain_rejected(self):
        p={'expr':['pow',an.X,3],'box':['-1','1']}
        c={'kind':'jet','order':3,'anchor':'0','tree':{'kind':'leaf','order':8,'bound':['6','6']}}
        self.assertFalse(ac.check(p,c))
    def test_original_domain_not_erased(self):
        p={'expr':['div',['c','0'],['x']],'box':['-1','1']}
        c={'kind':'interval','tree':{'kind':'leaf','order':8,'bound':['0','0']}}
        self.assertFalse(ac.check(p,c))
    def test_tree_cannot_skip_a_region(self):
        p={'expr':['c','1'],'box':['0','1']}
        leaf={'kind':'leaf','order':8,'bound':['1','1']}
        c={'kind':'interval','tree':{'kind':'split','at':'1','left':leaf,'right':leaf}}
        self.assertFalse(ac.check(p,c))
    def test_all_recorded_cases(self):
        path=Path(__file__).resolve().parents[2]/'results/certificates.json'
        for r in json.loads(path.read_text()):
            with self.subTest(lane=r['lane'],case=r['name']):
                checker={'poly':pc.check,'nc':nc.check,'analytic':ac.check}[r['lane']]
                self.assertEqual(checker(r['problem'],r['certificate']),r['certificate']['kind']!='unknown')
if __name__=='__main__':unittest.main()
