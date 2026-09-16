"""Shared representations, input validation, and a strict JSON boundary.

Search and checking share this module, but no solver algorithms. Fractions are
encoded as canonical [numerator, denominator] pairs. No floating-point input.
The limits are research limits, not a hostile-input hardening claim.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from math import gcd
import json
from typing import Any

class Invalid(ValueError):
    pass

def need(condition: bool, message: str) -> None:
    if not condition:
        raise Invalid(message)

def keys(obj: Any, wanted: set[str]) -> None:
    need(type(obj) is dict and set(obj) == wanted, "wrong object fields")

def integer(x: Any, lo: int = 0, hi: int = 1000000) -> int:
    need(type(x) is int and lo <= x <= hi, "invalid integer")
    return x

def array(x: Any, n: int | None = None) -> list:
    need(type(x) is list, "expected array")
    need(len(x) <= 100000, "array limit")
    if n is not None:
        need(len(x) == n, "wrong array length")
    return x

def ids(x: Any, n: int, allow_empty: bool = True) -> tuple[int, ...]:
    a = tuple(integer(v, 0, n - 1) for v in array(x))
    need(a == tuple(sorted(set(a))), "indices must be sorted and distinct")
    need(allow_empty or bool(a), "empty index set")
    return a

def rational(x: Any) -> Q:
    a = array(x, 2)
    num = integer(a[0], -(1 << 4096), 1 << 4096)
    den = integer(a[1], 1, 1 << 4096)
    need(gcd(abs(num), den) == 1, "noncanonical rational")
    return Q(num, den)

def encq(x: Q | int) -> list[int]:
    q = Q(x)
    return [q.numerator, q.denominator]

def distribution(x: Any, n: int | None = None) -> tuple[Q, ...]:
    a = tuple(rational(t) for t in array(x, n))
    need(bool(a) and all(t >= 0 for t in a) and sum(a) == 1,
         "not a probability distribution")
    return a

def encdist(x) -> list:
    return [encq(t) for t in x]

@dataclass(frozen=True)
class Arena:
    owner: tuple[int, ...]
    priority: tuple[int, ...]
    edges: tuple[tuple[int, ...], ...]
    @property
    def n(self): return len(self.owner)
    @classmethod
    def read(cls, x):
        keys(x, {"kind", "owner", "priority", "edges"})
        need(x["kind"] == "parity", "wrong problem kind")
        owners = tuple(integer(t, 0, 1) for t in array(x["owner"]))
        n = len(owners); need(0 < n <= 10000, "arena size")
        ps = tuple(integer(t, 0, 10000) for t in array(x["priority"], n))
        es = tuple(ids(t, n, False) for t in array(x["edges"], n))
        return cls(owners, ps, es)
    def obj(self):
        return {"kind": "parity", "owner": list(self.owner),
                "priority": list(self.priority), "edges": [list(e) for e in self.edges]}

@dataclass(frozen=True)
class Transport:
    mu: tuple[Q, ...]
    nu: tuple[Q, ...]
    relation: tuple[tuple[bool, ...], ...]
    @classmethod
    def read(cls, x):
        keys(x, {"kind", "mu", "nu", "relation"})
        need(x["kind"] == "transport", "wrong problem kind")
        mu, nu = distribution(x["mu"]), distribution(x["nu"])
        r = []
        for row in array(x["relation"], len(mu)):
            rr = tuple(array(row, len(nu)))
            need(all(type(t) is bool for t in rr), "relation is not Boolean")
            r.append(rr)
        return cls(mu, nu, tuple(r))
    def obj(self):
        return {"kind": "transport", "mu": encdist(self.mu), "nu": encdist(self.nu),
                "relation": [list(r) for r in self.relation]}

@dataclass(frozen=True)
class MDP:
    actions: tuple[tuple[tuple[Q, ...], ...], ...]
    terminal: tuple[int, ...]
    start: int
    @property
    def n(self): return len(self.actions)
    @classmethod
    def read(cls, x):
        keys(x, {"kind", "actions", "terminal", "start"})
        need(x["kind"] == "mdp", "wrong problem kind")
        rows = array(x["actions"]); n = len(rows)
        need(0 < n <= 2000, "MDP size")
        acts = []
        for row in rows:
            aa = tuple(distribution(d, n) for d in array(row))
            need(bool(aa), "deadlocked MDP state")
            acts.append(aa)
        ts = ids(x["terminal"], n)
        for s in ts:
            need(all(d[s] == 1 for d in acts[s]), "terminal is not absorbing")
        return cls(tuple(acts), ts, integer(x["start"], 0, n - 1))
    def obj(self):
        return {"kind": "mdp", "actions": [[encdist(d) for d in a] for a in self.actions],
                "terminal": list(self.terminal), "start": self.start}

@dataclass(frozen=True)
class Simulation:
    left: tuple[tuple[tuple[Q, ...], ...], ...]
    right: tuple[tuple[tuple[Q, ...], ...], ...]
    base: tuple[tuple[bool, ...], ...]
    @classmethod
    def read(cls, x):
        keys(x, {"kind", "left", "right", "base"})
        need(x["kind"] == "simulation", "wrong problem kind")
        def side(y):
            rows = array(y); n = len(rows); need(0 < n <= 1000, "system size")
            out = tuple(tuple(distribution(d, n) for d in array(a)) for a in rows)
            need(all(out), "deadlocked transition system")
            return out
        l, r = side(x["left"]), side(x["right"])
        base = tuple(tuple(array(row, len(r))) for row in array(x["base"], len(l)))
        need(all(type(v) is bool for row in base for v in row), "base relation type")
        return cls(l, r, base)
    def obj(self):
        return {"kind": "simulation", "left": [[encdist(d) for d in a] for a in self.left],
                "right": [[encdist(d) for d in a] for a in self.right],
                "base": [list(r) for r in self.base]}

def load_json(text: str):
    need(len(text) <= 100_000_000, "JSON size limit")
    def pairs(xs):
        out = {}
        for k, v in xs:
            need(k not in out, "duplicate JSON key")
            out[k] = v
        return out
    def no_float(x): raise Invalid("floating point and nonfinite numbers forbidden")
    def number(x):
        need(len(x) <= 1300, "integer digit limit")
        return int(x)
    return json.loads(text, object_pairs_hook=pairs, parse_float=no_float,
                      parse_constant=no_float, parse_int=number)
