from fractions import Fraction as Q
from forge_unbounded.model import Petri, PPS, Term
from forge_unbounded.search import petri_coverability, pps_enclosure, critical_extinction, scalar_algebraic
from forge_unbounded.verify import verify
p=Petri((1,0,0), (((1,0,0),(0,1,0)),((0,1,0),(1,0,0)),((0,0,0),(0,0,1))), ((0,2,0),))
c=petri_coverability(p)
print('mutex', c, verify(p,c))
s=PPS(((Term(Q(1,4),(0,)),Term(Q(3,4),(3,))),))
e=pps_enclosure(s, target_bits=24, rounding_bits=40)
print('cubic', len(e['ledger']), e['lower'], e['upper'], e['target_met'],verify(s,e))
a=scalar_algebraic(s,e,[Q(-1,4),Q(3,4),Q(3,4)],[Q(-1),Q(1)])
print('algebraic',verify(s,a))
t=PPS(((Term(Q(1,2),(0,0)),Term(Q(1,2),(1,1))), (Term(Q(1,2),(0,0)),Term(Q(1,2),(2,0)))))
f=critical_extinction(t)
print('critical',f,verify(t,f))
