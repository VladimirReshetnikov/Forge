#!/usr/bin/env python3
"""Small, self-contained examples; outputs are Python receipts, not Lean proofs."""
import json
from forgeq import search as S, checker as C
examples=[
 ('reach', {'actions':[[['1/2','1/4','1/4'],['0','2/3','1/3']],
                      [['0','1','0']],[['0','0','1']]], 'target':[2]}, S.reachability),
 ('runtime', {'actions':[[['1/2','1/2'],['3/4','1/4']],[['0','1']]],'target':[1]}, S.runtime),
 ('transport', S.transport_problem(['1/2','1/2'],['1/3','2/3'],cost=[[0,1],[1,0]]),S.transport),
 ('polynomial_cost',{'jumps':[-1,1],'probabilities':['2/3','1/3'],'cost':[0,1]},S.polynomial_cost),
]
for worker,problem,fn in examples:
    certificate=fn(problem)
    print(json.dumps({'worker':worker,'problem':problem,'certificate':certificate,
                     'audit':C.audit(worker,problem,certificate)},indent=2))
