"""Constructive one-variable integer projection with compressed CRT witnesses.

Input: inequalities a*y <= beta(x) and congruences a*y == beta(x) (mod m),
where a,m are fixed integers, m>0 and beta is an integer affine expression.
Output: a straight-line integer program w(x), an exact feasibility guard C(x),
and Bezout receipts. No modulus-sized residue table is constructed.
"""
from math import gcd


class Program:
    def __init__(self):
        self.nodes = []
        self.index = {}

    def emit(self, op, *args):
        key = (op,) + args
        if key not in self.index:
            self.index[key] = len(self.nodes)
            self.nodes.append(list(key))
        return self.index[key]

    def const(self, n):
        return self.emit('const', n)

    def scale(self, k, x):
        return self.emit('scale', k, x)

    def add(self, a, b):
        return self.emit('add', a, b)

    def sub(self, a, b):
        return self.add(a, self.scale(-1, b))

    def affine(self, coefficients):
        out = self.const(coefficients[0])
        for i, c in enumerate(coefficients[1:]):
            if c:
                out = self.add(out, self.scale(c, self.emit('var', i)))
        return out


def validate_problem(problem):
    n = problem['parameters']
    if type(n) is not int or n < 0:
        raise ValueError('invalid parameter count')
    for family in ['inequalities', 'congruences']:
        if type(problem[family]) is not list:
            raise ValueError('constraint list required')
        for row in problem[family]:
            if (type(row['a']) is not int or type(row['rhs']) is not list or
                len(row['rhs']) != n+1 or any(type(a) is not int for a in row['rhs'])):
                raise ValueError('invalid affine constraint')
            if family == 'congruences' and (type(row['m']) is not int or row['m'] <= 0):
                raise ValueError('positive integer modulus required')


def bezout(a, b):
    """Search routine. The certificate checker does not call this."""
    old_r, r = a, b
    old_u, u, old_v, v = 1, 0, 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r-q*r
        old_u, u = u, old_u-q*u
        old_v, v = v, old_v-q*v
    sign = -1 if old_r < 0 else 1
    return [sign*old_r, sign*old_u, sign*old_v]


def valid_bezout(a, b, receipt):
    if (type(receipt) is not list or len(receipt) != 3 or
        any(type(v) is not int for v in receipt)):
        return False
    g, u, v = receipt
    return g > 0 and a % g == 0 and b % g == 0 and u*a + v*b == g


def assemble(problem, receipts):
    """Deterministic certificate elaboration, given independently checked receipts.

    Shared by search and checker. Thus it is NOT an independent formal proof of
    the generator; the test suite differentially checks concrete semantics.
    """
    validate_problem(problem)
    if len(receipts) != 2*len(problem['congruences']):
        raise ValueError('incorrect receipt count')
    p = Program()
    guards = []
    zero = p.const(0)
    r, period = zero, 1
    for i, row in enumerate(problem['congruences']):
        a, m = row['a'], row['m']
        first, second = receipts[2*i:2*i+2]
        if not valid_bezout(a, m, first):
            raise ValueError('invalid normalization receipt')
        g, u, _ = first
        b = p.affine(row['rhs'])
        guards.append(['divides', g, b])
        modulus = m//g
        s = p.emit('mod', p.scale(u, p.emit('div', b, g)), modulus)
        if not valid_bezout(period, modulus, second):
            raise ValueError('invalid CRT receipt')
        h, v, _ = second
        difference = p.sub(s, r)
        guards.append(['divides', h, difference])
        k = p.emit('mod', p.scale(v, p.emit('div', difference, h)), modulus//h)
        new_period = period * (modulus//h)
        r = p.emit('mod', p.add(r, p.scale(period, k)), new_period)
        period = new_period
    lower, upper = [], []
    for row in problem['inequalities']:
        a, b = row['a'], p.affine(row['rhs'])
        if a > 0:
            upper.append(p.emit('div', b, a))
        elif a < 0:
            lower.append(p.scale(-1, p.emit('div', b, -a)))
        else:
            guards.append(['le', zero, b])
    def reduce_nodes(op, ns):
        result = ns[0]
        for z in ns[1:]:
            result = p.emit(op, result, z)
        return result
    L = reduce_nodes('max', lower) if lower else None
    U = reduce_nodes('min', upper) if upper else None
    if L is not None:
        witness = p.add(L, p.emit('mod', p.sub(r, L), period))
    elif U is not None:
        witness = p.sub(U, p.emit('mod', p.sub(U, r), period))
    else:
        witness = r
    if U is not None and L is not None:
        guards.append(['le', witness, U])
    return {'nodes': p.nodes, 'guards': guards, 'witness': witness,
            'period': period, 'residue': r}


def synthesize(problem):
    validate_problem(problem)
    receipts, period = [], 1
    for row in problem['congruences']:
        first = bezout(row['a'], row['m'])
        modulus = row['m']//first[0]
        second = bezout(period, modulus)
        receipts += [first, second]
        period *= modulus//second[0]
    program = assemble(problem, receipts)
    return {'schema': 'forge.integer-projection/1', 'problem': problem,
            'bezout': receipts, 'program': program}


def check(problem, certificate):
    try:
        if (certificate.get('schema') != 'forge.integer-projection/1' or
            certificate.get('problem') != problem):
            return False
        expected = assemble(problem, certificate['bezout'])
        # Avoid Python equality treating True as 1 or 1.0 as 1.
        def integral_tree(x):
            if isinstance(x, dict):
                return all(type(k) is str and integral_tree(v) for k, v in x.items())
            if isinstance(x, list):
                return all(integral_tree(v) for v in x)
            return type(x) in (int, str)
        return integral_tree(certificate['program']) and expected == certificate['program']
    except (KeyError, ValueError, TypeError, ZeroDivisionError, IndexError, AttributeError):
        return False


def evaluate_program(program, inputs):
    values = []
    for node in program['nodes']:
        op, *a = node
        if op == 'const': value = a[0]
        elif op == 'var': value = inputs[a[0]]
        elif op == 'scale': value = a[0] * values[a[1]]
        elif op == 'add': value = values[a[0]] + values[a[1]]
        elif op == 'div': value = values[a[0]] // a[1]
        elif op == 'mod': value = values[a[0]] % a[1]
        elif op == 'max': value = max(values[a[0]], values[a[1]])
        elif op == 'min': value = min(values[a[0]], values[a[1]])
        else: raise ValueError('unknown operation')
        values.append(value)
    feasible = True
    for op, a, b in program['guards']:
        feasible &= values[b] % a == 0 if op == 'divides' else values[a] <= values[b]
    return bool(feasible), values[program['witness']]


def holds(problem, xs, y):
    """Direct input semantics, independent of the generated instruction program."""
    def rhs(row):
        return row['rhs'][0] + sum(a*x for a, x in zip(row['rhs'][1:], xs))
    return (all(row['a']*y <= rhs(row) for row in problem['inequalities']) and
            all((row['a']*y-rhs(row)) % row['m'] == 0 for row in problem['congruences']))
