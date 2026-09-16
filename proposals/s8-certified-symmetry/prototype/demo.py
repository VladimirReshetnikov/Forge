"""Small executable examples. Run from prototype: python -S demo.py"""
import json
from forge_symmetry.producer import (named_problem,build_chain,burnside_certificate,
                                     canonical_family_certificate)
from forge_symmetry.checker import (verify_chain,verify_burnside,verify_canonical_family)
from forge_symmetry.reynolds_producer import project_certificate
from forge_symmetry.reynolds_checker import verify_projection

problem=named_problem('D',10)
chain=verify_chain(problem,build_chain(problem).export())
inventory=verify_burnside(chain,burnside_certificate(problem))
results={'D10':{'order':chain.order,'numerator':inventory.polynomial_numerator(),
                'binary_bracelets':inventory.count_colors(2),
                'three_color_bracelets':inventory.count_colors(3),
                'weight_five_binary_bracelets':inventory.count_binary_weight(5)}}
problem=named_problem('A',5);search=build_chain(problem)
chain=verify_chain(problem,search.export());colors=[1,0,2,3,4]
cert=canonical_family_certificate(search,colors,'A')
results['A5_canonical']=verify_canonical_family(chain,colors,cert)
problem=named_problem('S',4);chain=verify_chain(problem,build_chain(problem).export())
terms=[[[0,2,0,0],2,1],[[2,0,0,0],1,1]]
cert=project_certificate(problem,terms)
results['S4_Reynolds']=verify_projection(chain,terms,cert)
print(json.dumps(results,indent=2))
