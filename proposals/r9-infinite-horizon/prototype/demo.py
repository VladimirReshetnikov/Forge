#!/usr/bin/env python3
"""Small, deterministic demonstrations; no third-party packages required."""
from fractions import Fraction as F
from forge_horizon.models import PDS, Rule, Game, Chain
from forge_horizon import pushdown, games, markov
from forge_horizon.checkers import check_pds, check_game, check_chain
from forge_horizon.codec import dumps

def main() -> None:
    depth=30
    rules=(Rule(0,0,0,()),)+tuple(Rule(0,i,0,(i-1,i-1)) for i in range(1,depth+1))
    p=PDS(1,depth+1,rules,0,(depth,),frozenset({0}))
    print('COMPRESSED PUSHDOWN RUN (length computed from DAG, not expanded)')
    print(dumps(check_pds(p,pushdown.solve(p))))
    print('UNBOUNDED STACKS, UNREACHABLE TARGET')
    p=PDS(2,1,(Rule(0,0,0,(0,0)),Rule(0,0,0,())),0,(0,),frozenset({1}))
    print(dumps(check_pds(p,pushdown.solve(p))))
    edges=((0,1),(1,))
    for owner in (0,1):
        g=Game((owner,0),edges,frozenset({1}))
        c=games.solve(g);key='winning' if 0 in c['winning']['region'] else 'losing'
        print('EXIT CONTROLLED BY '+('PROTAGONIST' if owner==0 else 'ANTAGONIST'))
        print(dumps(check_game(g,c[key],0)))
    c=Chain(((F(3,4),F(1,4)),(F(0),F(1))),frozenset({1}),
            (F(0),F(1)),(F(3,2),F(0)))
    print('RANDOM EXIT: ALMOST-SURE ABSORPTION IS NOT EVERY-PATH TERMINATION')
    print(dumps(check_chain(c,markov.solve(c))))
    c=Chain(((F(0),F(2,3),F(1,3)),(F(0),F(1),F(0)),(F(0),F(0),F(1))),
            frozenset({1}),(F(0),F(1),F(0)),(F(1),F(0),F(1)))
    print('POSITIVE-PROBABILITY TRAP')
    print(dumps(check_chain(c,markov.solve(c))))

if __name__=='__main__':
    main()
