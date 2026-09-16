"""Optional external corroboration. Requires SymPy; not used by the checker.

Run: python optional_sympy_oracle.py > ../results/sympy_oracle.json
This is a different algorithm implementation, not a formal proof.
"""
import sys
if not __debug__:
    raise RuntimeError("Regression and replay scripts require assertions enabled; do not use -O")
import json
import random
import sympy
from sympy.combinatorics import Permutation, PermutationGroup
from forge_symmetry.producer import named_problem, build_chain, mul
from forge_symmetry.checker import verify_chain

a,b = (1,0,2),(0,2,1)
# SymPy's multiplication applies the LEFT factor first: the adapter reverses it.
assert tuple((Permutation(b)*Permutation(a)).array_form) == mul(a,b)
assert tuple((Permutation(a)*Permutation(b)).array_form) != mul(a,b)
rng = random.Random(20260915)
rows = []
for family,n in [('S',15),('S',30),('S',40),('A',12),('A',20),('D',50),('C',97)]:
    problem = named_problem(family,n)
    chain = verify_chain(problem,build_chain(problem).export())
    group = PermutationGroup([Permutation(g) for g in problem['generators']])
    assert int(group.order()) == chain.order
    for _ in range(20):
        query = list(range(n)); rng.shuffle(query)
        assert bool(group.contains(Permutation(query))) == chain.contains(query)
    rows.append({'case':f'{family}{n}', 'order':chain.order, 'membership_queries':20})
print(json.dumps({'status':'ALL_ASSERTIONS_PASSED', 'sympy':sympy.__version__,
 'composition_adapter':'our mul(a,b) = SymPy b*a (noncommuting fixture checked)',
 'order_comparisons':len(rows),'membership_comparisons':20*len(rows),'rows':rows},indent=2))
