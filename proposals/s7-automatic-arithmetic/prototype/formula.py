"""Small, explicit first-order syntax over unbounded natural numbers.
All coefficients are Python integers; multiplication of variables is unsupported.
Quantifiers bind names without shadowing an active variable. Sibling scopes may
reuse names. Constructors do not decide formulas.
"""
from __future__ import annotations
from copy import deepcopy
from typing import Any

Formula = dict[str, Any]

def eq(coeff: dict[str, int], rhs: int = 0) -> Formula:
    return {"op": "eq", "coeff": dict(coeff), "rhs": rhs}

def le(coeff: dict[str, int], rhs: int = 0) -> Formula:
    return {"op": "le", "coeff": dict(coeff), "rhs": rhs}

def cong(coeff: dict[str, int], rhs: int, modulus: int) -> Formula:
    return {"op": "cong", "coeff": dict(coeff), "rhs": rhs, "modulus": modulus}

def parity(var: str, value: int = 0) -> Formula:
    return {"op": "parity", "var": var, "value": value}

def pow2(var: str) -> Formula:
    return {"op": "pow2", "var": var}

def bitand(x: str, y: str, z: str) -> Formula:
    return {"op": "bitand", "vars": [x, y, z]}

def bitxor(x: str, y: str, z: str) -> Formula:
    return {"op": "bitxor", "vars": [x, y, z]}

def neg(arg: Formula) -> Formula:
    return {"op": "not", "arg": arg}

def binary(op: str, left: Formula, right: Formula) -> Formula:
    return {"op": op, "left": left, "right": right}

def And(left: Formula, right: Formula) -> Formula:
    return binary("and", left, right)

def Or(left: Formula, right: Formula) -> Formula:
    return binary("or", left, right)

def Iff(left: Formula, right: Formula) -> Formula:
    return binary("iff", left, right)

def Implies(left: Formula, right: Formula) -> Formula:
    return Or(neg(left), right)

def Exists(var: str, arg: Formula) -> Formula:
    return {"op": "exists", "var": var, "arg": arg}

def Forall(var: str, arg: Formula) -> Formula:
    # Universality has no separate certificate rule.
    return neg(Exists(var, neg(arg)))

def truth(value: bool) -> Formula:
    return {"op": "const", "value": value}

def rename_free(f: Formula, old: str, new: str) -> Formula:
    """Capture-avoiding rename. Rejects a binder that would capture `new`."""
    g = deepcopy(f)
    op = f["op"]
    if op in ("eq", "le", "cong"):
        if old in g["coeff"]:
            c = g["coeff"].pop(old)
            g["coeff"][new] = g["coeff"].get(new, 0) + c
    elif op in ("pow2", "parity"):
        if g["var"] == old:
            g["var"] = new
    elif op in ("bitand", "bitxor"):
        g["vars"] = [new if v == old else v for v in g["vars"]]
    elif op == "exists":
        if f["var"] == old:
            return g
        if f["var"] == new:
            raise ValueError("rename would capture a variable")
        g["arg"] = rename_free(f["arg"], old, new)
    elif op == "not":
        g["arg"] = rename_free(f["arg"], old, new)
    elif op in ("and", "or", "iff"):
        g["left"] = rename_free(f["left"], old, new)
        g["right"] = rename_free(f["right"], old, new)
    return g

def free_variables(f: Formula) -> set[str]:
    """Collect free names in the supported syntax (not an expression parser)."""
    op = f["op"]
    if op in ("eq", "le", "cong"):
        return set(f["coeff"])
    if op in ("pow2", "parity"):
        return {f["var"]}
    if op in ("bitand", "bitxor"):
        return set(f["vars"])
    if op == "exists":
        return free_variables(f["arg"]) - {f["var"]}
    if op == "not":
        return free_variables(f["arg"])
    if op in ("and", "or", "iff"):
        return free_variables(f["left"]) | free_variables(f["right"])
    if op == "const":
        return set()
    raise ValueError("unsupported formula")


def least_graph(relation: Formula, output: str, fresh: str) -> Formula:
    """R(x,y) and no smaller z satisfies R(x,z). No totality assumption."""
    if fresh == output or fresh in free_variables(relation):
        raise ValueError("least-graph variable is not fresh")
    smaller = le({fresh: 1, output: -1}, -1)
    alternative = rename_free(relation, output, fresh)
    return And(relation, neg(Exists(fresh, And(smaller, alternative))))
