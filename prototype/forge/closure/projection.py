# PROVENANCE: e8-invariant-ideals/prototype/presburger.py, ported with the
# house naming conventions. The algorithm, the Bezout receipt contract, the
# hash-consed program, and the disclosure below are that proposal's.
"""Exact one-output integer projection with a straight-line witness program.

Input is a conjunction over one existential integer output y:

    a*y <= beta(x)              inequalities
    a*y == beta(x)  (mod m)     congruences, m > 0

with integer coefficients and affine parameter right sides. Output is a
quantifier-free guard C(x) and a witness program w(x) with

    (exists y. Phi(x,y))  <->  C(x),    and   C(x) => Phi(x, w(x)).

The point is that no residue table is built. A modulus with a short binary
representation can make a table unaffordable -- a period of 10**18 is eighteen
digits to write and 10**18 rows to enumerate -- while the program stays linear
in the number of constraints.

WHAT IS AND IS NOT INDEPENDENT HERE. Each gcd arrives as a Bezout receipt
(g, u, v) and the checker verifies g > 0, g | c, g | m and u*c + v*m = g rather
than re-running the extended Euclidean algorithm; those four conditions already
force g to be the positive gcd. That much is a genuine asymmetry.

The rest is not, and this module says so rather than implying otherwise:
`assemble` is shared by the search and the checker. Replay therefore detects a
modified receipt or a modified program, but cannot by itself detect an
arithmetic mistake common to both uses of the assembler. The mitigation is a
different route -- `holds` evaluates the original constraints directly, and the
test suite compares the guard against an exhaustive concrete oracle over a
provably sufficient range -- not checker independence.

Outside the fragment: variable coefficients such as x*y <= z, variable moduli,
nonlinear parameter right sides, general Boolean combinations, and several
mutually constrained outputs. Disequalities would need explicit branching in a
later layer; they are not silently dropped. A one-output completeness theorem
is not complete Presburger synthesis.
"""
from __future__ import annotations

SCHEMA = 'forge.integer-projection/1'


class Program:
    """A hash-consed straight-line integer program.

    Nodes are const, var, scale, add, div (positive divisor), mod (positive
    modulus), max and min. No floating-point operation, no variable
    denominator, no implicit conversion to machine integers.
    """

    def __init__(self):
        self.nodes: list[list] = []
        self.index: dict[tuple, int] = {}

    def emit(self, op: str, *args) -> int:
        key = (op,) + args
        if key not in self.index:
            self.index[key] = len(self.nodes)
            self.nodes.append(list(key))
        return self.index[key]

    def const(self, n): return self.emit('const', n)
    def scale(self, k, x): return self.emit('scale', k, x)
    def add(self, a, b): return self.emit('add', a, b)
    def sub(self, a, b): return self.add(a, self.scale(-1, b))

    def affine(self, coefficients) -> int:
        out = self.const(coefficients[0])
        for i, c in enumerate(coefficients[1:]):
            if c:
                out = self.add(out, self.scale(c, self.emit('var', i)))
        return out


def validate_problem(problem) -> None:
    n = problem['parameters']
    if type(n) is not int or n < 0:
        raise ValueError('invalid parameter count')
    for family in ('inequalities', 'congruences'):
        if type(problem[family]) is not list:
            raise ValueError('constraint list required')
        for row in problem[family]:
            if (type(row['a']) is not int or type(row['rhs']) is not list or
                    len(row['rhs']) != n+1 or
                    any(type(a) is not int for a in row['rhs'])):
                raise ValueError('invalid affine constraint')
            if family == 'congruences' and (type(row['m']) is not int or row['m'] <= 0):
                raise ValueError('positive integer modulus required')


def bezout(a: int, b: int) -> list[int]:
    """Search routine. The certificate checker never calls this."""
    old_r, r = a, b
    old_u, u, old_v, v = 1, 0, 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q*r
        old_u, u = u, old_u - q*u
        old_v, v = v, old_v - q*v
    sign = -1 if old_r < 0 else 1
    return [sign*old_r, sign*old_u, sign*old_v]


def valid_bezout(a: int, b: int, receipt) -> bool:
    """The four conditions that force g to be the positive gcd of a and b."""
    if (type(receipt) is not list or len(receipt) != 3 or
            any(type(v) is not int for v in receipt)):
        return False
    g, u, v = receipt
    return g > 0 and a % g == 0 and b % g == 0 and u*a + v*b == g


def assemble(problem, receipts) -> dict:
    """Deterministic elaboration from the problem and its checked receipts.

    Shared by search and checker -- see the module docstring. The divisibility
    guards are never discarded: every quotient below is computed by floor
    division and is exact only under its own guard, so the expressions stay
    defined even when a guard is false.
    """
    validate_problem(problem)
    if len(receipts) != 2*len(problem['congruences']):
        raise ValueError('incorrect receipt count')
    p = Program()
    guards: list[list] = []
    zero = p.const(0)
    residue, period = zero, 1
    for i, row in enumerate(problem['congruences']):
        a, m = row['a'], row['m']
        first, second = receipts[2*i:2*i+2]
        if not valid_bezout(a, m, first):
            raise ValueError('invalid normalisation receipt')
        g, u, _ = first
        rhs = p.affine(row['rhs'])
        guards.append(['divides', g, rhs])
        modulus = m//g
        shifted = p.emit('mod', p.scale(u, p.emit('div', rhs, g)), modulus)
        if not valid_bezout(period, modulus, second):
            raise ValueError('invalid CRT receipt')
        h, v, _ = second
        difference = p.sub(shifted, residue)
        guards.append(['divides', h, difference])
        k = p.emit('mod', p.scale(v, p.emit('div', difference, h)), modulus//h)
        new_period = period*(modulus//h)
        residue = p.emit('mod', p.add(residue, p.scale(period, k)), new_period)
        period = new_period
    lower, upper = [], []
    for row in problem['inequalities']:
        a, rhs = row['a'], p.affine(row['rhs'])
        if a > 0:
            upper.append(p.emit('div', rhs, a))
        elif a < 0:
            # ceil(-beta/c) = -floor(beta/c) for c > 0. Truncation toward zero
            # gives wrong answers at negative parameters.
            lower.append(p.scale(-1, p.emit('div', rhs, -a)))
        else:
            guards.append(['le', zero, rhs])

    def fold(op, nodes):
        result = nodes[0]
        for node in nodes[1:]:
            result = p.emit(op, result, node)
        return result

    # No sentinel for a missing endpoint: this is unbounded Z, not a machine range.
    low = fold('max', lower) if lower else None
    high = fold('min', upper) if upper else None
    if low is not None:
        witness = p.add(low, p.emit('mod', p.sub(residue, low), period))
    elif high is not None:
        witness = p.sub(high, p.emit('mod', p.sub(high, residue), period))
    else:
        witness = residue
    if high is not None and low is not None:
        guards.append(['le', witness, high])
    return {'nodes': p.nodes, 'guards': guards, 'witness': witness,
            'period': period, 'residue': residue}


def synthesize(problem) -> dict:
    validate_problem(problem)
    receipts, period = [], 1
    for row in problem['congruences']:
        first = bezout(row['a'], row['m'])
        modulus = row['m']//first[0]
        second = bezout(period, modulus)
        receipts += [first, second]
        period *= modulus//second[0]
    return {'schema': SCHEMA, 'problem': problem, 'bezout': receipts,
            'program': assemble(problem, receipts)}


def evaluate(program, inputs) -> tuple[bool, int]:
    """Run an ALREADY CHECKED program. This is not a revalidation."""
    values: list[int] = []
    for node in program['nodes']:
        op, *a = node
        if op == 'const':
            value = a[0]
        elif op == 'var':
            value = inputs[a[0]]
        elif op == 'scale':
            value = a[0]*values[a[1]]
        elif op == 'add':
            value = values[a[0]] + values[a[1]]
        elif op == 'div':
            value = values[a[0]]//a[1]
        elif op == 'mod':
            value = values[a[0]] % a[1]
        elif op == 'max':
            value = max(values[a[0]], values[a[1]])
        elif op == 'min':
            value = min(values[a[0]], values[a[1]])
        else:
            raise ValueError('unknown operation')
        values.append(value)
    feasible = True
    for op, a, b in program['guards']:
        feasible &= values[b] % a == 0 if op == 'divides' else values[a] <= values[b]
    return bool(feasible), values[program['witness']]


def holds(problem, xs, y) -> bool:
    """The input semantics, evaluated directly and independently of the program."""
    def rhs(row):
        return row['rhs'][0] + sum(a*x for a, x in zip(row['rhs'][1:], xs))
    return (all(row['a']*y <= rhs(row) for row in problem['inequalities']) and
            all((row['a']*y - rhs(row)) % row['m'] == 0
                for row in problem['congruences']))


def large_period_example() -> dict:
    """Two nine-digit primes, a 60-bit period, and a 42-node program.

    The interval holds exactly one representative of every residue class, so
    the construction theorem gives feasibility for all x. At x = 0 the witness
    is 2,000,000,015. A residue table for this period is not a sensible
    representation -- which is a statement about representation size, not a
    measured speed comparison.
    """
    m1, m2 = 1_000_000_007, 1_000_000_009
    period = m1*m2
    return {'parameters': 1,
            'inequalities': [{'a': -1, 'rhs': [0, -1]},
                             {'a': 1, 'rhs': [period-1, 1]}],
            'congruences': [{'a': 1, 'rhs': [1, 2], 'm': m1},
                            {'a': 1, 'rhs': [-3, 5], 'm': m2}]}
