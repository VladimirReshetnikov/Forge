# PROVENANCE: e9-finite-summaries -- prototype/forge_summaries/ore_search.py
# (common-left-multiple search and the Cauchy cover) and the `ore_identity`
# and `singularity_plan` validators in its check.py. Reimplemented over the
# standard library: the original search used SymPy for its nullspace, this one
# does exact rational elimination, so the whole lane runs under `python -S`.
"""Common left multiples of recurrence operators, and singularity seed plans.

Shift operators do not commute with their coefficients:

    (a_i(n) E^i)(b_j(n) E^j) = a_i(n) b_j(n+i) E^(i+j),

so E*n = (n+1)*E, not n*E. Treating E as a commuting indeterminate produces the
wrong middle coefficient, and a test in this package rejects exactly that.

A certificate of a common LEFT multiple is three operators with

    L = U A = V B,

where the problem supplies A and B and the certificate may not redefine them.
If A annihilates f and B annihilates g, then L annihilates both -- and nothing
is claimed about minimality. A deliberately non-minimal multiple is allowed;
it just costs more seed obligations and possibly more apparent singularities,
which must then be accounted for rather than cancelled informally.

A nonvanishing leading coefficient is a hypothesis, not a formality. Knowing
p_r is a nonzero POLYNOMIAL is not enough, because a polynomial can be nonzero
as an expression and zero at a specific natural index. With

    Sigma = { s in N : p_r(s) = 0 },   I = {0..r-1} union { s+r : s in Sigma },

matching f and g on I forces f = g everywhere. The seed set is sufficient, not
minimal, and a seed at s rather than s+r is an off-by-order error that does not
repair the missing pivot.

The checker does not accept a producer's root list. It verifies an explicit
Cauchy bound, evaluates the leading coefficient at every integer in [0, B], and
recomputes the seed set. There is no floating-point root finding anywhere. The
enumeration is deliberately simple and sometimes wasteful: large coefficients
make B enormous, and the producer refuses bounds above 100000 -- a resource
policy, not a conclusion about roots.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import ceil
from typing import Sequence

MAX_BOUND = 100_000

# A polynomial is a tuple of Fractions, index = degree, no trailing zero.
Poly1 = tuple


def trim(coefficients: Sequence[Q]) -> Poly1:
    out = list(coefficients)
    while out and not out[-1]:
        out.pop()
    return tuple(out)


def poly(*coefficients) -> Poly1:
    return trim([Q(c) for c in coefficients])


def padd(a: Poly1, b: Poly1) -> Poly1:
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else Q(0)) + (b[i] if i < len(b) else Q(0))
                 for i in range(n)])


def pscale(a: Poly1, k) -> Poly1:
    return trim([c*Q(k) for c in a])


def psub(a: Poly1, b: Poly1) -> Poly1:
    return padd(a, pscale(b, -1))


def pmul(a: Poly1, b: Poly1) -> Poly1:
    if not a or not b:
        return ()
    out = [Q(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b):
            out[i+j] += x*y
    return trim(out)


def pshift(a: Poly1, s: int) -> Poly1:
    """p(n) -> p(n + s), by binomial expansion over exact rationals."""
    out: Poly1 = ()
    for degree, coefficient in enumerate(a):
        if not coefficient:
            continue
        term = (Q(1),)
        for _ in range(degree):
            term = pmul(term, (Q(s), Q(1)))
        out = padd(out, pscale(term, coefficient))
    return out


def peval(a: Poly1, x) -> Q:
    value = Q(0)
    for coefficient in reversed(a):
        value = value*Q(x) + coefficient
    return value


def ore_mul(u: Sequence[Poly1], a: Sequence[Poly1]) -> list[Poly1]:
    """Operator composition under (a_i E^i)(b_j E^j) = a_i(n) b_j(n+i) E^(i+j)."""
    if not u or not a:
        return []
    out = [()]*(len(u)+len(a)-1)
    for i, ui in enumerate(u):
        if not ui:
            continue
        for j, aj in enumerate(a):
            if not aj:
                continue
            out[i+j] = padd(out[i+j], pmul(ui, pshift(aj, i)))
    while out and not out[-1]:
        out.pop()
    return out


def _nullspace(rows: list[list[Q]], width: int) -> list[list[Q]]:
    """Exact rational nullspace of the row system, as a list of basis vectors."""
    matrix = [list(r) for r in rows]
    pivot_of = {}
    pivot_row = 0
    for col in range(width):
        sel = next((r for r in range(pivot_row, len(matrix)) if matrix[r][col]), None)
        if sel is None:
            continue
        matrix[pivot_row], matrix[sel] = matrix[sel], matrix[pivot_row]
        inverse = matrix[pivot_row][col]
        matrix[pivot_row] = [c/inverse for c in matrix[pivot_row]]
        for r in range(len(matrix)):
            if r != pivot_row and matrix[r][col]:
                factor = matrix[r][col]
                matrix[r] = [c - factor*p for c, p in zip(matrix[r], matrix[pivot_row])]
        pivot_of[col] = pivot_row
        pivot_row += 1
    basis = []
    for free in range(width):
        if free in pivot_of:
            continue
        vector = [Q(0)]*width
        vector[free] = Q(1)
        for col, row in pivot_of.items():
            vector[col] = -matrix[row][free]
        basis.append(vector)
    return basis


def _primitive(vector: list[Q]) -> list[Q]:
    """Clear denominators and the integer content; make the last nonzero positive."""
    from math import gcd
    denominator = 1
    for x in vector:
        denominator = denominator*x.denominator//gcd(denominator, x.denominator)
    integers = [int(x*denominator) for x in vector]
    content = 0
    for x in integers:
        content = gcd(content, abs(x))
    if content:
        integers = [x//content for x in integers]
    last = next((x for x in reversed(integers) if x), 0)
    if last < 0:
        integers = [-x for x in integers]
    return [Q(x) for x in integers]


def common_left_multiple(a: Sequence[Poly1], b: Sequence[Poly1],
                         multiplier_order: int, multiplier_degree: int):
    """Search for U, V of bounded order and degree with U A = V B.

    Any nonzero solution yields an acceptable L. A production system would
    delegate this to a dedicated Ore-algebra implementation; whatever that
    returns must still pass `certificates.check_ore`.
    """
    if not a or not b:
        raise ValueError('nonempty operators required')
    if multiplier_order < 0 or multiplier_degree < 0:
        raise ValueError('nonnegative bounds required')
    columns = []
    tags = []
    out_order = multiplier_order + max(len(a), len(b)) - 1
    for side, operator, sign in (('u', a, 1), ('v', b, -1)):
        for i in range(multiplier_order+1):
            for d in range(multiplier_degree+1):
                column: list[Poly1] = [()]*(out_order+1)
                monomial = tuple([Q(0)]*d + [Q(sign)])
                for j, aj in enumerate(operator):
                    if aj:
                        column[i+j] = padd(column[i+j],
                                           pmul(monomial, pshift(aj, i)))
                columns.append(column)
                tags.append((side, i, d))
    height = max((len(c[j]) for c in columns for j in range(out_order+1)), default=0)
    rows = []
    for j in range(out_order+1):
        for d in range(height):
            rows.append([c[j][d] if d < len(c[j]) else Q(0) for c in columns])
    stats = {'rows': len(rows), 'columns': len(columns),
             'multiplier_order': multiplier_order,
             'multiplier_degree': multiplier_degree}
    for vector in _nullspace(rows, len(columns)):
        vector = _primitive(vector)
        operators = []
        for side in ('u', 'v'):
            parts = []
            for i in range(multiplier_order+1):
                coefficients = [Q(0)]*(multiplier_degree+1)
                for value, (tag_side, tag_i, tag_d) in zip(vector, tags):
                    if tag_side == side and tag_i == i:
                        coefficients[tag_d] += value
                parts.append(trim(coefficients))
            while parts and not parts[-1]:
                parts.pop()
            operators.append(parts)
        u, v = operators
        if not u or not v:
            continue
        common = ore_mul(u, list(a))
        if common != ore_mul(v, list(b)):
            continue
        return ({'kind': 'ore-multiple', 'common': common,
                 'left_multiplier': u, 'right_multiplier': v}, stats)
    return None, stats


def cauchy_bound(leading: Poly1) -> int | None:
    """An integer B with every complex root of `leading` inside |z| <= B.

    If |z| > 1 + C with C = max |a_i/a_d|, then |z|^d <= C * sum |z|^i, which
    is at most C/(|z|-1) * |z|^d < |z|^d. A constant has no roots, so B = 0.
    Returns None when the bound exceeds the resource cap.
    """
    leading = trim(leading)
    if not leading:
        raise ValueError('leading coefficient must be a nonzero polynomial')
    degree = len(leading)-1
    if degree == 0:
        return 0
    top = leading[degree]
    ratio = 1 + max(abs(leading[i]/top) for i in range(degree))
    bound = ceil(ratio)
    return None if bound > MAX_BOUND else int(bound)


def singularity_cover(operator: Sequence[Poly1]):
    """The seed plan: {0..r-1} together with s+r for every natural root s.

    This verifies which values must be proved equal. It does not prove them,
    and it is not a proof that either sequence satisfies the recurrence.
    """
    order = len(operator)-1
    if order < 1:
        raise ValueError('order at least one required')
    bound = cauchy_bound(operator[-1])
    if bound is None:
        return None
    roots = [i for i in range(bound+1) if peval(operator[-1], i) == 0]
    return {'kind': 'singularity-cover', 'bound': bound,
            'singular_indices': roots,
            'seed_indices': sorted(set(range(order)) | {i+order for i in roots})}


def missed_singularity_example() -> list[Poly1]:
    """(n - 5)(f(n+1) - 2f(n)) = 0.

    The zero sequence and g(n) = 0 for n < 6, 2^(n-6) for n >= 6 both satisfy
    it. They agree at 0..5 and differ at 6, so six matching initial values do
    not settle a FIRST-ORDER recurrence. The required seed set is {0, 6}.
    """
    return [pmul(poly(-5, 1), poly(-2)), poly(-5, 1)]
