"""Transparent, synthetic cases. Not a held-out Lean benchmark."""
from __future__ import annotations
import random
import sympy as sp
from .search import machine, Limits
from .kripke import atom, bot, imp, conj, disj, neg, sequent

SEED=20260915

def machine_cases():
    x=sp.symbols('x0:8');u,v=sp.symbols('u0:2')
    a,b,c,d=x[:4]
    out=[]
    def put(name,p,expected='proved',limits=Limits(),family='worked'):
        out.append({'name':name,'family':family,'problem':p,'expected':expected,'limits':limits})
    delayed=machine(4,1,[0]*4,[(0,0,'read',[a+b,b+u,c+d,d+u])],[[a-c]])
    put('delayed_relational_equality',delayed)
    put('delayed_mutant',machine(4,1,[0]*4,[(0,0,'read',[a+b,b+u,c+d,d+u+1])],[[a-c]]),'refuted')
    put('sum_scaling',machine(2,1,[0,0],[(0,0,'read',[a+u,b+7*u])],[[b-7*a]]))
    put('square_of_sum',machine(2,1,[0,0],[(0,0,'read',[a+u,b+2*a*u+u*u])],[[b-a*a]]))
    put('cube_of_sum',machine(2,1,[0,0],[(0,0,'read',[a+u,b+3*a*a*u+3*a*u*u+u**3])],[[b-a**3]]))
    put('symmetric_polynomial',machine(3,1,[0,0,0],[(0,0,'read',[a+u,b+u*u,c+a*u])],[[a*a-b-2*c]]))
    put('fibonacci_relational',machine(4,0,[0,1,1,0],[(0,0,'step',[b,a+b,c+d,c])],[[b-c]]))
    put('alternating_control',machine(2,1,[0,0],[(0,1,'even',[a+u,u-b]),(1,0,'odd',[a-u,u-b])],
                                              [[a+b],[a-b]],nodes=2))
    put('circle_rotation',machine(2,0,[1,0],[(0,0,'rotate',[-b,a])],[[a*a+b*b-1]]))
    trap=sp.prod(u-i for i in range(7))
    put('seven_sample_trap',machine(1,1,[0],[(0,0,'read',[a+trap])],[[a]]),'refuted')
    put('nonlinear_growth_true_but_unknown',machine(1,0,[0],[(0,0,'square',[a*a])],[[a]]),'unknown',Limits(max_degree=8))
    put('empty_basis_zero_goal',machine(1,1,[3],[(0,0,'read',[a+u])],[[0]]))
    put('zero_step_failure',machine(1,0,[1],[],[[a]]),'refuted')
    put('unreachable_bad_node',machine(1,0,[0],[(0,0,'stay',[a])],[[a],[a-1]],nodes=2))
    put('simultaneous_swap',machine(2,0,[1,2],[(0,0,'swap',[b,a])],[[a+b-3]]))
    # Two payloads, polynomial input coefficients and state-affine dynamics.
    put('two_payload_square',machine(2,2,[0,0],[(0,0,'read',[a+u*v,b+2*a*u*v+(u*v)**2])],[[b-a*a]]))
    # A distinguished initialization edge models universally quantified
    # starting data using the same arbitrary-payload semantics.
    put('symbolic_initial_parameter',machine(2,1,[0,0],
        [(0,1,'initialize',[u,7*u]),(1,1,'read',[a+u,b+7*u])],[[],[b-7*a]],nodes=2))
    put('symbolic_initial_mutant',machine(2,1,[0,0],
        [(0,1,'initialize',[u,7*u+u*u]),(1,1,'read',[a+u,b+7*u])],[[],[b-7*a]],nodes=2),'refuted')
    rng=random.Random(SEED)
    for k in range(24):
        dim=2+(k%2);xs=sp.Matrix(x[:dim]);ys=sp.Matrix(x[dim:2*dim])
        U=sp.eye(dim)
        for i in range(dim):
            U[i,i]=rng.choice([-2,-1,1,2])
            for j in range(i+1,dim):U[i,j]=rng.randint(-2,2)
        Ui=U.inv();offset=sp.Matrix([rng.randint(-2,2) for _ in range(dim)])
        ini=sp.Matrix([rng.randint(-2,2) for _ in range(dim)])
        updates=[]
        for tag in range(1+(k%2)):
            A=sp.Matrix(dim,dim,[rng.randint(-2,2) for _ in range(dim*dim)])
            B=sp.Matrix([rng.randint(-2,2) for _ in range(dim)])
            C=sp.Matrix([rng.randint(-2,2) for _ in range(dim)])
            f=A*xs+B*u+C
            g=U*(A*(Ui*(ys-offset))+B*u+C)+offset
            updates.append((0,0,f'tag{tag}',list(f)+list(g)))
        # Only ONE of the hidden relational equations is provided as the goal.
        goal=ys[0]-(U*xs+offset)[0]
        initial=list(ini)+list(U*ini+offset)
        p=machine(2*dim,1,initial,updates,[[goal]])
        put(f'affine_conjugacy_{k:02}',p,family='conjugacy')
        badupdates=[]
        for src,dst,label,fs in updates:
            fs=list(fs);fs[dim]+=1
            badupdates.append((src,dst,label,fs))
        put(f'affine_conjugacy_mutant_{k:02}',machine(2*dim,1,initial,badupdates,[[goal]]),
            'refuted',family='conjugacy_mutant')
    return out


def logical_cases():
    p,q,r=map(atom,['P','Q','R'])
    negative=[
        ('atomic_implication',imp(p,q),[],1),
        ('excluded_middle',disj(p,neg(p)),[],2),
        ('double_negation_elimination',imp(neg(neg(p)),p),[],2),
        ('peirce',imp(imp(imp(p,q),p),p),[],2),
        ('weak_excluded_middle',disj(neg(p),neg(neg(p))),[],3),
        ('linearity',disj(imp(p,q),imp(q,p)),[],3),
        ('contextual_failure',q,[p],1),
        ('disjunction_does_not_select',p,[disj(p,q)],1),
    ]
    positive=[
        ('identity',imp(p,p)),
        ('composition',imp(imp(p,q),imp(imp(q,r),imp(p,r)))),
        ('conjunction_projection',imp(conj(p,q),p)),
        ('disjunction_injection',imp(p,disj(p,q))),
        ('ex_falso',imp(bot(),p)),
        ('double_negation_introduction',imp(p,neg(neg(p)))),
        ('disjunction_elimination',imp(disj(p,q),imp(imp(p,r),imp(imp(q,r),r)))),
        ('noncontradiction',neg(conj(p,neg(p)))),
    ]
    cases=[{'name':name,'problem':sequent(g,ctx),'expected':'ipc_countermodel','min_worlds':worlds}
           for name,g,ctx,worlds in negative]
    # Expected UNKNOWN here means this bounded refuter must not find a model;
    # its exhaustion is not being used as a proof of these schemas.
    cases += [{'name':name,'problem':sequent(g),'expected':'unknown'} for name,g in positive]
    return cases
