"""Deterministic tests and a finite-language differential oracle.

The oracle enumerates every derivation of its acyclic grammars. It does not
use the producer's span routines or either producer/checker evaluation routine.
Run: python -S -m unittest -v tests
"""
from __future__ import annotations
import copy
from fractions import Fraction as Q
from itertools import product
import json
import random
import tempfile
import unittest
from pathlib import Path

import checker
import compilers as c
import search as s


def finite_values(problem):
    """Exact exhaustive values for grammars whose child sorts precede parents."""
    answer={}
    for sort, dimension in problem['sorts'].items():
        values=set()
        for op in problem['operations']:
            if op['out']!=sort:
                continue
            assert all(child in answer for child in op['inputs']), 'not an acyclic grammar'
            for children in product(*(answer[child] for child in op['inputs'])):
                output=[Q(0)]*dimension
                for entry in op['terms']:
                    a=Q(entry['q'])
                    for i,index in enumerate(entry['in']):
                        a=a*children[i][index]
                    output[entry['out']]=output[entry['out']]+a
                values.add(tuple(output))
        answer[sort]=values
    return answer


def finite_truth(problem):
    values=finite_values(problem)
    valid=all(sum((Q(a)*b for a,b in zip(t['q'],v)),Q(0))==0
              for t in problem['targets'] for v in values[t['sort']])
    return valid, sum(map(len,values.values()))


def finite_paired_observations(original, quotient):
    """Exhaust every derivation of the paired acyclic models, without spans.

    We compare matching derivations, not just the two sets of final outputs.
    """
    def evaluate(model, op, children):
        result = [Q(0)] * model['sorts'][op['out']]
        for term in op['terms']:
            value = Q(term['q'])
            for slot, coordinate in enumerate(term['in']):
                value *= children[slot][coordinate]
            result[term['out']] += value
        return tuple(result)
    reachable = {}
    comparisons = 0
    for sort in original['sorts']:
        values = set()
        for op, small_op in zip(original['operations'], quotient['operations']):
            if op['out'] != sort:
                continue
            for children in product(*(reachable[s] for s in op['inputs'])):
                lhs = evaluate(original, op, [x[0] for x in children])
                rhs = evaluate(quotient, small_op, [x[1] for x in children])
                values.add((lhs, rhs))
        reachable[sort] = values
        for a, b in zip(original['targets'], quotient['targets']):
            if a['sort'] != sort:
                continue
            for lhs, rhs in values:
                left = sum((Q(x)*y for x,y in zip(a['q'],lhs)),Q(0))
                right = sum((Q(x)*y for x,y in zip(b['q'],rhs)),Q(0))
                if left != right:
                    return False, comparisons
                comparisons += 1
    return True, comparisons


def random_acyclic(seed):
    """Three sorts, two nullaries and two binary levels; rational tensors.

    Half the instances have a forced zero last coordinate in every operation,
    with a nonzero target selecting it. Others have unrestricted random data.
    """
    rng=random.Random(seed)
    dimension=rng.choice((2,3))
    forced=seed%2==0
    sorts={f'S{i}':dimension for i in range(3)}
    operations=[]
    for level,sort in enumerate(sorts):
        for which in range(2):
            inputs=[] if level==0 else [f'S{level-1}']*(1+which)
            terms=[]
            for out in range(dimension-int(forced)):
                for indices in product(range(dimension),repeat=len(inputs)):
                    a=Q(rng.randint(-2,2),rng.choice((1,1,2,3)))
                    if a:terms.append(c.term(out,indices,a))
            operations.append({'name':f'op_{level}_{which}','out':sort,
                               'inputs':inputs,'terms':terms})
    target=[str(int(i==dimension-1)) for i in range(dimension)]
    return {'schema':'forge.mlc.problem.v1','name':f'acyclic_{seed}',
            'sorts':sorts,'operations':operations,
            'targets':[{'sort':'S2','q':target}]}


def mutation_cases():
    """Deliberately invalid certificates/problems, each with a semantic reason."""
    p=c.leaf_count();cert=s.saturate(p)['certificate'];cases=[]
    def altered(label,change):
        pp,cc=copy.deepcopy(p),copy.deepcopy(cert)
        change(pp,cc);cases.append((label,pp,cc))
    altered('missing closure',lambda p,t:t['closures'].pop())
    altered('duplicate closure',lambda p,t:t['closures'].append(copy.deepcopy(t['closures'][0])))
    altered('false coefficient',lambda p,t:t['closures'][0]['coeff'].__setitem__(0,'2'))
    altered('target not annihilated',lambda p,t:p['targets'][0]['q'].__setitem__(0,'0'))
    altered('noncanonical fraction',lambda p,t:t['basis']['T'][0].__setitem__(0,'2/2'))
    altered('float coefficient',lambda p,t:t['basis']['T'][0].__setitem__(0,1.0))
    altered('boolean index',lambda p,t:t['closures'][0].__setitem__('op',False))
    altered('unknown certificate field',lambda p,t:t.__setitem__('trusted',True))
    altered('tensor/source mismatch',lambda p,t:p['operations'][0]['terms'][0].__setitem__('q','2'))
    altered('missing basis vector',lambda p,t:t['basis']['T'].pop())
    p2=c.dyck(True);ct=s.saturate(p2)['certificate']
    for label,change in [
      ('cyclic witness',lambda t:t['nodes'][1].__setitem__('children',[1])),
      ('wrong witness value',lambda t:t.__setitem__('claimed_value','-1')),
      ('invalid root',lambda t:t.__setitem__('root',100)),
      ('missing witness child',lambda t:t['nodes'][1].__setitem__('children',[]))]:
        cc=copy.deepcopy(ct);change(cc);cases.append((label,copy.deepcopy(p2),cc))
    # A certificate of nonzero output must not be accepted after replacing its
    # authoritative source by the balanced, output-zero transition system.
    cases.append(('transplanted witness',c.dyck(),copy.deepcopy(ct)))
    order=c.noncommuting_control();ct=s.saturate(order)['certificate'];ct['claimed_value']='1'
    cases.append(('reversed matrix convention',order,ct))
    noisy=c.leaf_count(True);qc=s.minimize(noisy)['certificate']
    for label,field in [('invalid left inverse','left_inverses'),('invalid section','sections')]:
        cc=copy.deepcopy(qc);x=Q(cc[field]['T'][0][0]);cc[field]['T'][0][0]=str(x+1)
        cases.append((label,copy.deepcopy(noisy),cc))
    cc=copy.deepcopy(qc);cc['model']['targets'][0]['q'][0]=str(Q(cc['model']['targets'][0]['q'][0])+1)
    cases.append(('quotient observation drift',copy.deepcopy(noisy),cc))
    cc=copy.deepcopy(qc);cc['model']['operations'][0]['terms'][0]['q']='2'
    cases.append(('quotient constructor drift',copy.deepcopy(noisy),cc))
    return cases


class ExactTests(unittest.TestCase):
    def accepted(self,p,r):
        self.assertIn('certificate',r)
        ans=checker.verify(p,r['certificate'])
        self.assertTrue(ans['accepted'],ans)
        return ans

    def test_tree_identity(self):
        p=c.leaf_count();r=s.saturate(p)
        self.assertEqual(r['status'],'PROVED');self.accepted(p,r)
        self.assertEqual(r['stats']['ranks'],{'T':2})

    def test_dyck_positive_and_negative(self):
        for bad in (False,True):
            p=c.dyck(bad);r=s.saturate(p);a=self.accepted(p,r)
            self.assertEqual(r['status'],'REFUTED' if bad else 'PROVED')
            if bad:self.assertEqual(a['word_length'],'2')

    def test_noncommutative_order(self):
        p=c.noncommuting_control();a=self.accepted(p,s.saturate(p))
        self.assertEqual(a['value'],'-1')

    def test_exponential_compressed_witness(self):
        p=c.exponential_word(60);a=self.accepted(p,s.saturate(p))
        self.assertEqual(a['dag_nodes'],61)
        self.assertEqual(a['word_length'],str(2**60))
        self.assertEqual(a['expanded_tree_nodes'],str(2**61-1))

    def test_context_quotient(self):
        p=c.leaf_count(True);r=s.minimize(p);self.accepted(p,r)
        self.assertEqual(r['stats']['reachable_dimensions'],{'T':4})
        self.assertEqual(r['stats']['quotient_dimensions'],{'T':2})

    def test_acyclic_exhaustive_differential(self):
        for seed in range(240):
            with self.subTest(seed=seed):
                p=random_acyclic(10000+seed);truth,_=finite_truth(p)
                r=s.saturate(p);self.accepted(p,r)
                self.assertEqual(r['status'],'PROVED' if truth else 'REFUTED')

    def test_acyclic_quotients(self):
        for seed in range(40):
            with self.subTest(seed=seed):
                p=random_acyclic(20000+seed);r=s.minimize(p);self.accepted(p,r)
                ok,_=finite_paired_observations(p,r['certificate']['model'])
                self.assertTrue(ok)

    def test_echelon_coordinates(self):
        rng=random.Random(4911)
        for dimension in range(1,8):
            e=s.Echelon(dimension)
            for _ in range(30):
                v=tuple(Q(rng.randint(-4,4),rng.randint(1,5)) for _ in range(dimension))
                e.add(v);coeff=e.coordinates(v)
                self.assertIsNotNone(coeff)
                self.assertEqual(s.lincomb(e.basis,coeff,dimension),v)
            L=s.left_inverse(e.basis,dimension)
            for i,row in enumerate(L):
                for j,v in enumerate(e.basis):self.assertEqual(s.dot(row,v),int(i==j))

    def test_semantic_and_parser_mutations(self):
        for label,p,cert in mutation_cases():
            with self.subTest(label=label):
                self.assertFalse(checker.verify(p,cert)['accepted'])

    def test_no_constant_means_empty_language(self):
        p={'schema':'forge.mlc.problem.v1','name':'empty_language','sorts':{'S':1},
           'operations':[{'name':'cycle','out':'S','inputs':['S'],
                          'terms':[c.term(0,[0],1)]}],
           'targets':[{'sort':'S','q':['1']}]}
        r=s.saturate(p);a=self.accepted(p,r)
        self.assertEqual(a['closure_identities'],0)
        self.assertEqual(r['certificate']['basis']['S'],[])

    def test_zero_nullary_is_not_omitted(self):
        p={'schema':'forge.mlc.problem.v1','name':'zero','sorts':{'S':1},
           'operations':[{'name':'zero','out':'S','inputs':[],'terms':[]}],
           'targets':[{'sort':'S','q':['1']}]}
        r=s.saturate(p);a=self.accepted(p,r)
        self.assertEqual(a['closure_identities'],1)
        self.assertEqual(r['certificate']['basis']['S'],[])

    def test_each_recursive_slot_is_scheduled(self):
        p={'schema':'forge.mlc.problem.v1','name':'slot_sensitive','sorts':{'S':2},
           'operations':[{'name':'a','out':'S','inputs':[],'terms':[c.term(0,[],1)]},
                         {'name':'b','out':'S','inputs':[],'terms':[c.term(1,[],1)]},
                         {'name':'skew','out':'S','inputs':['S','S'],
                          'terms':[c.term(0,[0,1],1),c.term(1,[1,0],-1)]}],
           'targets':[{'sort':'S','q':['0','0']}]}
        r=s.saturate(p);self.accepted(p,r)
        self.assertEqual(len(r['certificate']['closures']),6)
        self.assertEqual(r['stats']['candidate_evaluations'],6)

    def test_ternary_constructor(self):
        p={'schema':'forge.mlc.problem.v1','name':'ternary','sorts':{'S':1},
           'operations':[{'name':'one','out':'S','inputs':[],'terms':[c.term(0,[],1)]},
                         {'name':'three','out':'S','inputs':['S']*3,'terms':[c.term(0,[0]*3,1)]}],
           'targets':[{'sort':'S','q':['0']}]}
        r=s.saturate(p);self.accepted(p,r);self.assertEqual(len(r['certificate']['closures']),2)

    def test_redundant_cover_allowed(self):
        p={'schema':'forge.mlc.problem.v1','name':'redundant','sorts':{'S':1},
           'operations':[{'name':'one','out':'S','inputs':[],'terms':[c.term(0,[],1)]}],
           'targets':[{'sort':'S','q':['0']}]}
        cert={'schema':'forge.mlc.certificate.v1','kind':'invariant',
              'basis':{'S':[['1'],['2']]},
              'closures':[{'op':0,'children':[],'coeff':['1','0']}]}
        self.assertTrue(checker.verify(p,cert)['accepted'])

    def test_source_rejects_same_child_nonlinearity(self):
        op={'name':'square','out':'S','inputs':['S'],
            'polynomials':[[c.monomial(1,(0,0),(0,0))]]}
        with self.assertRaises(ValueError):c.multiaffine('bad',{'S':1},[op],[])

    def test_resource_cutoffs(self):
        p=c.leaf_count()
        for budget in (s.Budget(max_candidates=0),s.Budget(max_basis=0)):
            r=s.saturate(p,budget);self.assertEqual(r['status'],'UNKNOWN')
            self.assertNotIn('certificate',r)
        p=c.exponential_word(10)
        p['source']['matrices']['a']=[['2']]
        p['operations'][0]['terms'][0]['q']='2'
        r=s.saturate(p,s.Budget(max_bits=64))
        self.assertEqual(r['status'],'UNKNOWN')
        self.assertEqual(r['reason'],'coefficient_bit_limit')

    def test_duplicate_json_key_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'bad.json';path.write_text('{"x":1,"x":2}')
            with self.assertRaises(checker.Invalid):checker.load(path)

    def test_zero_dimensional_quotient(self):
        p=c.leaf_count();r=s.minimize(p);a=self.accepted(p,r)
        self.assertEqual(a['quotient_dimensions'],{'T':0})

if __name__=='__main__':unittest.main()
