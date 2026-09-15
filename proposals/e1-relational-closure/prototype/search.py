"""Target-directed linear-span and polynomial-ideal closure (untrusted search).

SymPy is used only in discovery and certificate construction. The independent
stdlib checker imports no code from this file. Polynomial updates are total,
simultaneous, over Q, with arbitrary fresh rational inputs and finitely many
control locations. This file does not implement a Lean tactic.
"""
from __future__ import annotations
from dataclasses import dataclass,field
from itertools import product
import time
from typing import Any,Literal
import sympy as s


def rat(x: Any) -> list[str]:
    q=s.Rational(x)
    return [str(q.p),str(q.q)]


def poly_json(expr: Any,variables: tuple) -> list:
    expr=s.expand(expr)
    if not variables:
        return [] if expr==0 else [[[],rat(expr)]]
    p=s.Poly(expr,*variables,domain=s.QQ)
    return [[list(m),rat(c)] for m,c in sorted(p.terms()) if c]


@dataclass
class Edge:
    src: int
    dst: int
    inputs: tuple
    update: tuple


@dataclass
class System:
    name: str
    x: tuple
    parameters: tuple
    locations: int
    initial: list[tuple[int,tuple]]
    edges: list[Edge]
    targets: list[tuple[int,Any]]

    def json(self) -> dict:
        return dict(schema='forge-polynomial-system-v1',name=self.name,n=len(self.x),
                    locations=self.locations,parameters=len(self.parameters),
                    initial=[dict(location=l,state=[poly_json(p,self.parameters) for p in v]) for l,v in self.initial],
                    edges=[dict(src=e.src,dst=e.dst,inputs=len(e.inputs),
                                update=[poly_json(p,self.x+e.inputs) for p in e.update]) for e in self.edges],
                    targets=[dict(location=l,polynomial=poly_json(p,self.x)) for l,p in self.targets])


@dataclass
class Limits:
    degree: int=12
    generators: int=80
    pullbacks: int=500
    coefficient_terms: int=3000
    grid_points: int=100_000
    seconds: float=25.0


@dataclass
class Node:
    loc: int
    p: Any
    parent: int | None=None
    edge: int | None=None
    coefficient: tuple=()
    target: int | None=None


class Exhausted(RuntimeError):
    pass


def substitute(p: Any,x: tuple,F: tuple) -> Any:
    return s.expand(s.sympify(p).subs(dict(zip(x,F,strict=True)),simultaneous=True))


def input_coefficients(p: Any,us: tuple) -> list[tuple[tuple,Any]]:
    p=s.expand(p)
    if not us:
        return [((),p)] if p!=0 else []
    return [(m,s.expand(c)) for m,c in sorted(s.Poly(p,*us).terms()) if c!=0]


def linear_coordinates(p: Any,B: list,vs: tuple) -> list | None:
    p=s.expand(p)
    if not B:
        return [] if p==0 else None
    polys=[s.Poly(q,*vs,domain=s.QQ).as_dict() for q in [*B,p]]
    monomials=sorted(set().union(*(q.keys() for q in polys)))
    if not monomials:
        return [s.Integer(0)]*len(B)
    M=s.Matrix([[q.get(m,0) for q in polys[:-1]] for m in monomials])
    y=s.Matrix([polys[-1].get(m,0) for m in monomials])
    try:
        sol,free=M.gauss_jordan_solve(y)
    except ValueError:
        return None
    return [s.expand(c.subs({v:0 for v in free})) for c in sol]


class Closure:
    def __init__(self,P: System,mode: Literal['linear','ideal'],limits: Limits | None=None):
        if mode not in ('linear','ideal'):
            raise ValueError('mode must be linear or ideal')
        self.P=P
        self.mode=mode
        self.limits=limits or Limits()
        self.nodes: list[Node]=[]
        self.at: list[list[int]]=[[] for _ in range(P.locations)]
        self.gb: dict[int,Any]={}
        self.started=time.perf_counter()
        self.stats={'pullbacks':0,'membership_queries':0,'groebner_calls':0,
                    'generators':0,'max_generated_degree':0,'grid_evaluations':0}
        self.refutation: dict | None=None

    def tick(self) -> None:
        if time.perf_counter()-self.started>self.limits.seconds:
            raise Exhausted('cooperative wall-time limit; a CAS call is not preempted')

    def basis(self,loc: int) -> list:
        ps=[self.nodes[i].p for i in self.at[loc]]
        if self.mode=='linear' or not ps:
            return ps
        if loc not in self.gb:
            self.tick()
            self.stats['groebner_calls']+=1
            self.gb[loc]=s.groebner(ps,*self.P.x,order='grevlex',domain=s.QQ)
        return [p.as_expr() for p in self.gb[loc].polys]

    def coordinates(self,p: Any,loc: int) -> list | None:
        self.stats['membership_queries']+=1
        B=self.basis(loc)
        if self.mode=='linear':
            return linear_coordinates(p,B,self.P.x)
        if not B:
            return [] if s.expand(p)==0 else None
        q,r=self.gb[loc].reduce(s.expand(p))
        return q if r==0 else None

    def nonzero_point(self,p: Any,variables: tuple) -> tuple:
        p=s.expand(p)
        if p==0:
            raise RuntimeError('nonzero_point called on zero polynomial')
        if not variables:
            return ()
        pp=s.Poly(p,*variables,domain=s.QQ)
        ranges=[range(int(pp.degree(v))+1) for v in variables]
        for values in product(*ranges):
            self.stats['grid_evaluations']+=1
            if self.stats['grid_evaluations']>self.limits.grid_points:
                raise Exhausted('exact witness-grid budget')
            self.tick()
            if substitute(p,variables,values)!=0:
                return tuple(s.Integer(v) for v in values)
        raise RuntimeError('interpolation-grid lemma violated')

    def witness(self,node_id: int,initial_id: int,pullback: Any) -> dict:
        P=self.P
        parameters=self.nonzero_point(pullback,P.parameters)
        loc,init=P.initial[initial_id]
        state=tuple(substitute(p,P.parameters,parameters) for p in init)
        steps=[]
        i=node_id
        while self.nodes[i].parent is not None:
            node=self.nodes[i]
            parent=self.nodes[node.parent]
            edge=P.edges[node.edge]
            if loc!=edge.src or parent.loc!=edge.dst:
                raise RuntimeError('internal provenance/control-flow mismatch')
            image=substitute(parent.p,P.x,edge.update)
            at_state=substitute(image,P.x,state)
            inputs=self.nonzero_point(at_state,edge.inputs)
            state=tuple(substitute(substitute(p,P.x,state),edge.inputs,inputs) for p in edge.update)
            steps.append(dict(edge=node.edge,inputs=[rat(v) for v in inputs]))
            loc=edge.dst
            i=node.parent
        root=self.nodes[i]
        if root.target is None or P.targets[root.target][0]!=loc or substitute(root.p,P.x,state)==0:
            raise RuntimeError('internal witness reconstruction failure')
        return dict(schema='forge-counterexample-v1',initial=initial_id,
                    parameters=[rat(v) for v in parameters],steps=steps,target=root.target)

    def consider(self,node: Node) -> None:
        self.tick()
        node.p=s.expand(node.p)
        if node.p==0:
            return
        degree=int(s.Poly(node.p,*self.P.x).total_degree())
        self.stats['max_generated_degree']=max(self.stats['max_generated_degree'],degree)
        # A positive degree-cap failure is UNKNOWN, never a counterexample.
        if degree>self.limits.degree:
            raise Exhausted('generated-polynomial degree cap')
        if len(s.Poly(node.p,*self.P.x).terms())>self.limits.coefficient_terms:
            raise Exhausted('generated-polynomial term cap')
        if self.coordinates(node.p,node.loc) is not None:
            return
        if len(self.nodes)>=self.limits.generators:
            raise Exhausted('independent-generator cap')
        node_id=len(self.nodes)
        self.nodes.append(node)
        self.at[node.loc].append(node_id)
        self.gb.pop(node.loc,None)
        self.stats['generators']=len(self.nodes)
        for initial_id,(loc,initial) in enumerate(self.P.initial):
            if loc==node.loc:
                image=substitute(node.p,self.P.x,initial)
                if image!=0:
                    self.refutation=self.witness(node_id,initial_id,image)
                    return

    def certificate(self) -> dict:
        P=self.P
        B=[self.basis(l) for l in range(P.locations)]
        targets=[]
        for loc,p in P.targets:
            cs=self.coordinates(p,loc)
            if cs is None:
                raise RuntimeError('target missing from final ideal/span')
            targets.append([poly_json(q,P.x) for q in cs])
        matrices=[]
        for edge in P.edges:
            rows=[]
            for g in B[edge.dst]:
                image=substitute(g,P.x,edge.update)
                quotients=[s.Integer(0)]*len(B[edge.src])
                for m,p in input_coefficients(image,edge.inputs):
                    cs=self.coordinates(p,edge.src)
                    if cs is None:
                        raise RuntimeError('closure did not stabilize')
                    monomial=s.prod(v**e for v,e in zip(edge.inputs,m,strict=True))
                    quotients=[s.expand(q+c*monomial) for q,c in zip(quotients,cs,strict=True)]
                rows.append([poly_json(q,P.x+edge.inputs) for q in quotients])
            matrices.append(rows)
        return dict(schema='forge-closure-cert-v1',basis=[[poly_json(g,P.x) for g in b] for b in B],
                    target=targets,step=matrices)

    def run(self) -> dict:
        try:
            for target,(loc,p) in enumerate(self.P.targets):
                self.consider(Node(loc,p,target=target))
                if self.refutation is not None:
                    break
            head=0
            while self.refutation is None and head<len(self.nodes):
                node=self.nodes[head]
                for ei,e in enumerate(self.P.edges):
                    if e.dst!=node.loc:
                        continue
                    self.stats['pullbacks']+=1
                    if self.stats['pullbacks']>self.limits.pullbacks:
                        raise Exhausted('pullback budget')
                    self.tick()
                    image=substitute(node.p,self.P.x,e.update)
                    for monomial,p in input_coefficients(image,e.inputs):
                        self.consider(Node(e.src,p,parent=head,edge=ei,coefficient=monomial))
                        if self.refutation is not None:
                            break
                    if self.refutation is not None:
                        break
                head+=1
            if self.refutation is not None:
                result={'status':'refuted','evidence':self.refutation}
            else:
                result={'status':'proved','evidence':self.certificate()}
        except Exhausted as error:
            result={'status':'unknown','reason':str(error)}
        self.stats['elapsed_seconds']=time.perf_counter()-self.started
        result.update(mode=self.mode,stats=self.stats)
        return result


def solve(P: System,mode: Literal['linear','ideal']='ideal',limits: Limits | None=None) -> dict:
    return Closure(P,mode,limits).run()
