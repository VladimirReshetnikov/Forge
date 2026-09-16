"""Behavioral, adversarial, and semantic-boundary tests. Standard library only."""
import copy, itertools, json, tempfile, unittest
from pathlib import Path
from fractions import Fraction as F
from ncforge.algebra import *
from ncforge.search import *
from ncforge.checker import verify, load_json, Rejected, evaluate_matrix, Meter
from experiments import comm, anticom, examples, determinant, principal_psd

def qmat(A): return [[[int(x),1] for x in row] for row in A]
def vector(v): return [[int(x),1] for x in v]
def matrix_cert(ms,v):
    return {'schema':'ncforge.certificate.v1','kind':'matrix_countermodel',
            'dimension':len(v),'matrices':[qmat(M) for M in ms],'vector':vector(v)}

class AlgebraTests(unittest.TestCase):
    def setUp(self): self.x,self.y=var(0),var(1)
    def test_word_order_not_commuted(self):
        self.assertNotEqual(mul(self.x,self.y),mul(self.y,self.x))
    def test_star_reverses_and_maps_atoms(self):
        p={(0,0,1):F(2)}
        self.assertEqual(star(p,(1,0)),{(0,1,1):F(2)})
    def test_fractional_coefficients_exact(self):
        p=add(scale(self.x,F(1,3)),scale(self.x,F(1,7)))
        self.assertEqual(p,{(0,):F(10,21)})
    def test_zero_and_empty_word(self):
        self.assertEqual(mul(one(),self.x),self.x)
        self.assertEqual(power(self.x,0),one())
    def test_homogeneous_gram_empty_target(self):
        self.assertTrue(verify(problem({},[],2,'operator'),homogeneous_sos({},2))['accepted'])
    def test_off_diagonal_without_pivot_is_not_psd(self):
        self.assertIsNone(ldl_squares([[F(0),F(1)],[F(1),F(0)]]))
    def test_zero_diagonal_psd_branch(self):
        d=ldl_squares([[F(0),F(0)],[F(0),F(3)]])
        self.assertEqual(d,[(F(3),[F(0),1])])
    def test_ldl_exact_reconstruction(self):
        Q=[[F(1),F(2),F(-1)],[F(2),F(5),F(0)],[F(-1),F(0),F(9)]]
        ds=ldl_squares(Q); self.assertIsNotNone(ds)
        R=[[sum((a*v[i]*v[j] for a,v in ds),F(0)) for j in range(3)] for i in range(3)]
        self.assertEqual(R,Q)
    def test_echelon_provenance_expands(self):
        ps=[add(self.x,self.y),add(self.x,self.y,-1),scale(self.x,3)]
        e=Echelon()
        for i,p in enumerate(ps): e.insert(p,i)
        c=e.solve(self.y); t={}
        for i,a in c.items(): t=add(t,ps[i],a)
        self.assertEqual(t,self.y)
    def test_slicing_preserves_the_answer(self):
        p=comm(power(self.x,3),self.y);rs=[comm(self.x,self.y)]
        for enabled in (False,True):
            c=equality_search(p,rs,2,4,slice_support=enabled)
            self.assertTrue(verify(problem(p,rs,2),c['certificate'])['accepted'])
    def test_inhomogeneous_countermodel_producer_refuses(self):
        rs=[add(mul(self.x,self.y),one(),-1)]
        self.assertIsNone(quotient_countermodel(add(mul(self.y,self.x),one(),-1),rs,2))
    def test_homogeneous_target_requires_even_degree(self):
        self.assertIsNone(homogeneous_sos(self.x,2))
    def test_search_budget_failure_is_not_a_proof(self):
        with self.assertRaises(BudgetExceeded): contexts([self.x],2,5,max_columns=1)
    def test_cyclic_decomposition(self):
        p=comm(self.x,comm(self.x,self.y))
        cs=commutator_receipt(p)
        cert={'schema':'ncforge.certificate.v1','kind':'trace','ideal':[],
              'squares':[],'commutators':cs}
        self.assertTrue(verify(problem(p,[],2,'trace'),cert)['accepted'])
    def test_cyclic_nonzero_rejected(self):
        with self.assertRaises(ValueError): commutator_receipt(self.x)

class CheckerTests(unittest.TestCase):
    def setUp(self):
        x,y=var(0),var(1)
        r=add(mul(x,y),mul(y,x),-1)
        self.p=problem(add(mul(power(x,2),y),mul(y,power(x,2)),-1),[r],2)
        self.c=equality_search(add(mul(power(x,2),y),mul(y,power(x,2)),-1),[r],2,3)['certificate']
        self.op=problem(power(x,2),[],2,'operator')
        self.oc=homogeneous_sos(power(x,2),2)
    def reject(self,p,c): self.assertFalse(verify(p,c)['accepted'])
    def test_valid_receipt(self): self.assertTrue(verify(self.p,self.c)['accepted'])
    def test_wrong_original_target(self):
        p=copy.deepcopy(self.p);p['target']=[[[0],1,1]];self.reject(p,self.c)
    def test_weight_mutation(self):
        c=copy.deepcopy(self.c);c['ideal'][0]['weight']=[2,1];self.reject(self.p,c)
    def test_left_right_placement_mutation(self):
        c=copy.deepcopy(self.c); c['ideal'][0]['left'],c['ideal'][0]['right']=c['ideal'][0]['right'],c['ideal'][0]['left'];self.reject(self.p,c)
    def test_missing_hypothesis(self):
        p=copy.deepcopy(self.p);p['relations']=[];self.reject(p,self.c)
    def test_replaced_hypothesis(self):
        p=copy.deepcopy(self.p);p['relations']=[[[[0],1,1]]];self.reject(p,self.c)
    def test_certificate_cannot_redefine_problem(self):
        c=copy.deepcopy(self.c);c['target']=[];self.reject(self.p,c)
    def test_negative_square_weight(self):
        c=copy.deepcopy(self.oc);c['squares'][0]['weight']=[-1,1];self.reject(self.op,c)
    def test_float_rejected(self):
        c=copy.deepcopy(self.c);c['ideal'][0]['weight']=[1.0,1];self.reject(self.p,c)
    def test_boolean_rejected(self):
        c=copy.deepcopy(self.c);c['ideal'][0]['weight']=[True,1];self.reject(self.p,c)
    def test_zero_denominator(self):
        c=copy.deepcopy(self.c);c['ideal'][0]['weight']=[1,0];self.reject(self.p,c)
    def test_unreduced_fraction(self):
        c=copy.deepcopy(self.c);c['ideal'][0]['weight']=[2,2];self.reject(self.p,c)
    def test_oversized_rational(self):
        c=copy.deepcopy(self.c);c['ideal'][0]['weight']=[1<<8193,1];self.reject(self.p,c)
    def test_out_of_range_letter(self):
        c=copy.deepcopy(self.c);c['ideal'][0]['left']=[2];self.reject(self.p,c)
    def test_duplicate_polynomial_word(self):
        p=copy.deepcopy(self.p);p['target'].append(p['target'][0]);self.reject(p,self.c)
    def test_zero_monomial_forbidden(self):
        p=copy.deepcopy(self.p);p['target']=[[[0],0,1]];self.reject(p,self.c)
    def test_involution_must_square_to_identity(self):
        p=copy.deepcopy(self.p);p['involution']=[1,1];self.reject(p,self.c)
    def test_switched_involution_changes_square(self):
        p=copy.deepcopy(self.op);p['involution']=[1,0];self.reject(p,self.oc)
    def test_interpretation_tag_mismatch(self):
        c=copy.deepcopy(self.oc);c['kind']='trace';c['commutators']=[];self.reject(self.op,c)
    def test_operator_cannot_include_trace_remainder(self):
        c=copy.deepcopy(self.oc);c['commutators']=[];self.reject(self.op,c)
    def test_unsupported_fixed_dimension_metadata_refused(self):
        p=copy.deepcopy(self.p);p['matrix_dimension']=2;self.reject(p,self.c)
    def test_unsupported_scalar_domain_refused(self):
        p=copy.deepcopy(self.p);p['field']='F2';self.reject(p,self.c)
    def test_equality_schema_cannot_drop_positive_premises(self):
        p=copy.deepcopy(self.p);p['positives']=[[[[0],1,1]]];self.reject(p,self.c)
    def test_trace_mode_cannot_accept_algebra_countermodel(self):
        p=problem(var(0),[],1,'trace');c=matrix_cert([[[1]]],[1]);self.reject(p,c)
    def test_matrix_relation_checked_not_only_on_vector(self):
        p=problem(one(),[var(0)],1)
        # X v=0 but X != 0; checking relations on v alone would falsely accept.
        c=matrix_cert([[[0,0],[0,1]]],[1,0]);self.reject(p,c)
    def test_target_must_separate_matrix_vector(self):
        p=problem(var(0),[],1);c=matrix_cert([[[0]]],[1]);self.reject(p,c)
    def test_valid_small_matrix_counterexample(self):
        p=problem(var(0),[],1);c=matrix_cert([[[2]]],[1]);self.assertTrue(verify(p,c)['accepted'])
    def test_countermodel_dimension_mutation(self):
        p=problem(var(0),[],1);c=matrix_cert([[[2]]],[1]);c['dimension']=2;self.reject(p,c)
    def test_json_duplicate_keys_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            f=Path(d)/'bad.json';f.write_text('{"a":1,"a":2}')
            with self.assertRaises(Rejected): load_json(f)
    def test_json_nan_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            f=Path(d)/'bad.json';f.write_text('{"a":NaN}')
            with self.assertRaises(Rejected): load_json(f)

class SemanticTests(unittest.TestCase):
    def test_positive_matrices_do_not_multiply_positively(self):
        A=[[F(1),F(0)],[F(0),F(0)]];B=[[F(1),F(1)],[F(1),F(1)]]
        self.assertTrue(principal_psd(A));self.assertTrue(principal_psd(B))
        p=anticom(var(0),var(1));M=evaluate_matrix(p,[A,B],2,Meter());v=[F(1),F(-2)]
        q=sum((v[i]*M[i][j]*v[j] for i in range(2) for j in range(2)),F(0))
        self.assertEqual(q,-2)
    def test_trace_positive_but_operator_negative(self):
        x,y=var(0),var(1); p=add(one(),comm(x,comm(x,y)),2)
        A=[[F(1),F(0)],[F(0),F(0)]];B=[[F(0),F(1)],[F(1),F(0)]]
        M=evaluate_matrix(p,[A,B],2,Meter());v=[1,-1]
        self.assertEqual(sum(M[i][i] for i in range(2)),2)
        self.assertEqual(sum(v[i]*M[i][j]*v[j] for i in range(2) for j in range(2)),-2)
        c=dictionary_sos(p,[],[],[one()],2,3,kind='trace')
        self.assertTrue(verify(problem(p,[],2,'trace'),c)['accepted'])
        c['kind']='operator'
        self.assertFalse(verify(problem(p,[],2,'operator'),c)['accepted'])
    def test_positive_congruence_needs_assumption(self):
        x,y=var(0),var(1);p=mul(mul(y,x),y)
        c=dictionary_sos(p,[],[x],[y],2,3)
        self.assertTrue(verify(problem(p,[],2,'operator',[x]),c)['accepted'])
        self.assertFalse(verify(problem(p,[],2,'operator'),c)['accepted'])
    def test_modulo_self_adjointness_is_not_syntactic(self):
        A,D,B,C=[var(i) for i in range(4)]
        S=add(mul(A,add(B,C)),mul(D,add(B,C,-1)))
        p=add(scale(one(),8),power(S,2),-1)
        self.assertNotEqual(star(p,(0,1,2,3)),p)
        self.assertIsNone(dictionary_sos(p,[],[],[one()],4,4))
    def test_paired_star_atoms_valid(self):
        q=add(var(0),scale(var(1),2));p=mul(star(q,(1,0)),q)
        c=homogeneous_sos(p,2,(1,0))
        self.assertTrue(verify(problem(p,[],2,'operator',involution=(1,0)),c)['accepted'])
    def test_all_worked_examples(self):
        for name,p,c,meta in examples():
            with self.subTest(name=name): self.assertTrue(verify(p,c)['accepted'])
    def test_inhomogeneous_high_degree_needed(self):
        row=next(row for row in examples() if row[0]=='push_through')
        self.assertEqual(row[3]['bounds_2_3_4'],['unknown']*3)
    def test_automatic_involution_dictionary_has_six_rays(self):
        row=next(row for row in examples() if row[0]=='chsh_squared_bound')
        self.assertEqual(row[3]['generated_rays'],6)
    def test_chsh_all_24_atom_renamings(self):
        A,D,B,C=[var(i) for i in range(4)]
        rs=[add(power(t,2),one(),-1) for t in (A,D,B,C)]+[comm(s,t) for s in (A,D) for t in (B,C)]
        S=add(mul(A,add(B,C)),mul(D,add(B,C,-1)))
        p=add(scale(one(),8),mul(star(S,(0,1,2,3)),S),-1)
        for perm in itertools.permutations(range(4)):
            rename=lambda f:{tuple(perm[i] for i in w):c for w,c in f.items()}
            target=rename(p);rels=[rename(r) for r in rs]
            qs=involution_dictionary(rels,4)
            c=dictionary_sos(target,rels,[],qs,4,4,max_support=3)
            with self.subTest(perm=perm): self.assertTrue(verify(problem(target,rels,4,'operator'),c)['accepted'])
    def test_dictionary_requires_recognized_involutions(self):
        self.assertEqual(involution_dictionary([comm(var(0),var(1))],2),[])
    def test_zero_polynomial_relation_harmless(self):
        p=comm(var(0),var(1));rs=[{},p]
        c=equality_search(p,rs,2,2)['certificate']
        self.assertTrue(verify(problem(p,rs,2),c)['accepted'])
    def test_constant_relation_explodes_algebra(self):
        p=var(0);rs=[one()];c=equality_search(p,rs,1,1)['certificate']
        self.assertTrue(verify(problem(p,rs,1),c)['accepted'])
        self.assertIsNone(quotient_countermodel(p,rs,1))

if __name__=='__main__': unittest.main(verbosity=2)
