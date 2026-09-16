"""Small input models. Checkers receive these independently of certificates."""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F

class Invalid(ValueError):
    """An ill-formed input or a certificate that does not prove its claim."""

def require(condition: bool, message: str) -> None:
    if not condition:
        raise Invalid(message)

def natural(x: object, bound: int | None = None) -> bool:
    return type(x) is int and x >= 0 and (bound is None or x < bound)

@dataclass(frozen=True)
class Rule:
    p: int
    a: int
    q: int
    rhs: tuple[int, ...]

@dataclass(frozen=True)
class PDS:
    n: int
    alphabet: int
    rules: tuple[Rule, ...]
    start: int
    stack: tuple[int, ...]
    finals: frozenset[int]

    def validate(self) -> None:
        require(natural(self.n) and self.n > 0, 'positive control count')
        require(natural(self.alphabet) and self.alphabet > 0, 'positive alphabet')
        require(natural(self.start, self.n), 'start control')
        require(all(natural(q, self.n) for q in self.finals), 'final controls')
        require(all(natural(a, self.alphabet) for a in self.stack), 'initial stack')
        for r in self.rules:
            require(natural(r.p,self.n) and natural(r.q,self.n), 'rule control')
            require(natural(r.a,self.alphabet), 'rule symbol')
            require(len(r.rhs) <= 2 and all(natural(a,self.alphabet) for a in r.rhs),
                    'right hand side must have length at most two')

@dataclass(frozen=True)
class Game:
    owner: tuple[int, ...]       # 0: protagonist; 1: antagonist
    edges: tuple[tuple[int, ...], ...]
    accepting: frozenset[int]

    @property
    def n(self) -> int:
        return len(self.owner)

    def validate(self) -> None:
        require(self.n > 0 and len(self.edges) == self.n, 'game dimensions')
        require(all(type(x) is int and x in (0,1) for x in self.owner), 'owner')
        require(all(natural(v,self.n) for v in self.accepting), 'accepting set')
        for row in self.edges:
            require(len(row)>0 and len(row)==len(set(row)), 'total, duplicate-free arena')
            require(all(natural(v,self.n) for v in row), 'edge endpoint')

@dataclass(frozen=True)
class Chain:
    matrix: tuple[tuple[F, ...], ...]
    terminal: frozenset[int]
    payoff: tuple[F, ...]       # terminal payoffs in [0,1]; zero elsewhere
    cost: tuple[F, ...]         # nonnegative cost per nonterminal visit
    start: int = 0

    @property
    def n(self) -> int:
        return len(self.matrix)

    def validate(self) -> None:
        require(self.n > 0 and natural(self.start,self.n), 'chain start')
        require(len(self.payoff)==len(self.cost)==self.n, 'reward dimensions')
        require(all(natural(t,self.n) for t in self.terminal), 'terminal states')
        for s,row in enumerate(self.matrix):
            require(len(row)==self.n, 'matrix dimensions')
            require(all(type(p) is F and p>=0 for p in row), 'exact nonnegative probabilities')
            require(sum(row,F(0))==1, 'stochastic row')
            require(type(self.cost[s]) is F and self.cost[s]>=0, 'nonnegative exact cost')
            require(type(self.payoff[s]) is F and 0<=self.payoff[s]<=1, 'payoff in [0,1]')
            if s in self.terminal:
                require(row[s]==1 and self.cost[s]==0, 'terminal must be absorbing, cost zero')
            else:
                require(self.payoff[s]==0, 'nonterminal payoff must be zero')
