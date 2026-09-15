# PROVENANCE: e5-finite-certificates (the search, the D-1 bound, and the
# delayed-error fixtures that attain it), e6-finite-certificates-b (reporting
# closures and separating words as two outcomes rather than one success rate),
# e9-finite-summaries (the certificate shape checked here: basis G, target
# coordinates t, one action matrix C_a per letter).
"""Target-directed observable-space closure over a finite alphabet.

The goal is

    for every word w over the alphabet,   q A_w s0 = 0,
    with A_{a1...at} = A_at ... A_a1.

Start from the target row q and close the row space under right multiplication
by every action. Either every admitted row annihilates s0 -- and the closure is
an inductive invariant, certified by

    q = t G,      G A_a = C_a G,      G s0 = 0

-- or some admitted row does not, and its recorded word is a counterexample,
replayed in the ORIGINAL matrices before it is reported.

Two things this module does not do. It decides nothing about a constrained
input language: all words are permitted, and restricting them needs either a
product with an explicitly supplied automaton or a separate proof. And a run
cut off by a budget returns `unknown`, which never means the goal is false.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Sequence

Row = tuple[Q, ...]
Matrix = tuple[Row, ...]


def rational(x) -> Q:
    """Accept int, Fraction, 'n/d', or [numerator, denominator].

    Floats and bools are rejected outright rather than coerced: a float in a
    certificate is a defect, not an input format.
    """
    if isinstance(x, bool) or isinstance(x, float):
        raise TypeError('exact rationals only')
    if isinstance(x, Q):
        return x
    if isinstance(x, int):
        return Q(x)
    if isinstance(x, str):
        return Q(x)
    if isinstance(x, (list, tuple)) and len(x) == 2:
        num, den = x
        if isinstance(num, bool) or isinstance(den, bool):
            raise TypeError('exact rationals only')
        if not isinstance(num, int) or not isinstance(den, int) or den <= 0:
            raise ValueError('positive denominator required')
        return Q(num, den)
    raise TypeError('unsupported rational encoding')


def as_row(v: Sequence, width: int | None = None) -> Row:
    if isinstance(v, (str, bytes)):
        raise TypeError('row must be a sequence of rationals')
    row = tuple(rational(x) for x in v)
    if width is not None and len(row) != width:
        raise ValueError('row width mismatch')
    return row


def as_matrix(m: Sequence, rows: int | None = None, cols: int | None = None) -> Matrix:
    if isinstance(m, (str, bytes)):
        raise TypeError('matrix must be a sequence of rows')
    out = tuple(as_row(r, cols) for r in m)
    if rows is not None and len(out) != rows:
        raise ValueError('row count mismatch')
    if out and len({len(r) for r in out}) != 1:
        raise ValueError('ragged matrix')
    return out


def vec_mat(v: Row, m: Matrix) -> Row:
    """Row vector times matrix: (v M)_j = sum_i v_i M_ij."""
    if not m:
        return ()
    width = len(m[0])
    return tuple(sum((v[i]*m[i][j] for i in range(len(v))), Q(0))
                 for j in range(width))


def mat_mat(a: Matrix, b: Matrix) -> Matrix:
    return tuple(vec_mat(row, b) for row in a)


def dot(v: Row, w: Row) -> Q:
    return sum((x*y for x, y in zip(v, w)), Q(0))


def encode(value) -> list:
    """Rationals as [numerator, denominator] pairs, recursively. JSON-safe."""
    if isinstance(value, Q):
        return [value.numerator, value.denominator]
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


@dataclass(frozen=True)
class Model:
    """A rational state machine with one scalar observation.

    Matrices are stored row-wise in the row-vector convention, so `vec_mat`
    computes q A_a directly. `initial` is the column s0.
    """
    dimension: int
    initial: Row
    output: Row
    actions: tuple[Matrix, ...]

    @staticmethod
    def build(dimension: int, initial, output, actions) -> 'Model':
        if not isinstance(dimension, int) or isinstance(dimension, bool) or dimension < 1:
            raise ValueError('positive dimension required')
        acts = tuple(as_matrix(a, dimension, dimension) for a in actions)
        if not acts:
            raise ValueError('at least one action required')
        return Model(dimension, as_row(initial, dimension),
                     as_row(output, dimension), acts)

    def evaluate(self, word: Sequence[int]) -> Q:
        """Observation after reading `word`, in the original matrices.

        The word is read left to right, so the matrices multiply right to left:
        this is the A_{a1...at} = A_at ... A_a1 convention stated above, and it
        is the reason `search` prepends a letter when it right-multiplies.
        """
        row = self.output
        for letter in reversed(list(word)):
            if not isinstance(letter, int) or isinstance(letter, bool):
                raise TypeError('letters are action indices')
            if not 0 <= letter < len(self.actions):
                raise ValueError('letter out of range')
            row = vec_mat(row, self.actions[letter])
        return dot(row, self.initial)


class _Echelon:
    """Incremental exact row-echelon basis. Search side only."""

    def __init__(self, width: int):
        self.width = width
        self.rows: list[Row] = []
        self.pivots: list[int] = []

    def add(self, row: Row) -> bool:
        """Insert if independent of what is already here; report whether it was."""
        current = list(row)
        for basis_row, pivot in zip(self.rows, self.pivots):
            if current[pivot]:
                factor = current[pivot]
                current = [c - factor*b for c, b in zip(current, basis_row)]
        pivot = next((i for i, c in enumerate(current) if c), None)
        if pivot is None:
            return False
        inverse = current[pivot]
        self.rows.append(tuple(c/inverse for c in current))
        self.pivots.append(pivot)
        return True


def solve_coordinates(basis: Sequence[Row], target: Row) -> list[Q] | None:
    """Exact solution of x B = target, or None if there is none."""
    n = len(basis)
    if n == 0:
        return [] if not any(target) else None
    width = len(target)
    aug = [[basis[i][j] for i in range(n)] + [target[j]] for j in range(width)]
    where = [-1]*n
    pivot_row = 0
    for col in range(n):
        sel = next((r for r in range(pivot_row, width) if aug[r][col]), None)
        if sel is None:
            continue
        aug[pivot_row], aug[sel] = aug[sel], aug[pivot_row]
        inverse = aug[pivot_row][col]
        aug[pivot_row] = [c/inverse for c in aug[pivot_row]]
        for r in range(width):
            if r != pivot_row and aug[r][col]:
                factor = aug[r][col]
                aug[r] = [c - factor*p for c, p in zip(aug[r], aug[pivot_row])]
        where[col] = pivot_row
        pivot_row += 1
    for r in range(width):
        if not any(aug[r][:n]) and aug[r][n]:
            return None
    return [aug[where[c]][n] if where[c] >= 0 else Q(0) for c in range(n)]


def search(model: Model, max_rows: int | None = None) -> dict:
    """Close the observable row space, or return a separating word.

    Three outcomes, reported as three different results rather than as one
    success flag -- a separating word is an answer, not a failure:

      {'status': 'closure',    'certificate': ...}
      {'status': 'separating', 'word': [...], 'value': ...}
      {'status': 'unknown',    'reason': ...}
    """
    limit = model.dimension if max_rows is None else max_rows
    basis_rows: list[Row] = []
    echelon = _Echelon(model.dimension)
    queue: list[tuple[Row, tuple[int, ...]]] = [(model.output, ())]
    expansions = 0
    while queue:
        row, word = queue.pop(0)
        # Tested before the dependence check, so the counterexample route is
        # easy to audit: a dependent row cannot hide a nonzero observation.
        value = dot(row, model.initial)
        if value:
            replayed = model.evaluate(word)
            if replayed != value:
                raise AssertionError('separating word failed its own replay')
            return {'status': 'separating', 'word': list(word), 'value': replayed,
                    'stats': {'basis_size': len(basis_rows), 'expansions': expansions}}
        if not echelon.add(row):
            continue
        basis_rows.append(row)
        if len(basis_rows) > limit:
            return {'status': 'unknown', 'reason': 'row budget',
                    'stats': {'basis_size': len(basis_rows), 'expansions': expansions}}
        for letter, action in enumerate(model.actions):
            expansions += 1
            queue.append((vec_mat(row, action), (letter,) + word))
    basis = tuple(basis_rows)
    target = solve_coordinates(basis, model.output)
    if target is None:
        raise AssertionError('target not in its own closure')
    actions = []
    for action in model.actions:
        rows = []
        for row in basis:
            coords = solve_coordinates(basis, vec_mat(row, action))
            if coords is None:
                raise AssertionError('closure basis is not closed')
            rows.append(tuple(coords))
        actions.append(tuple(rows))
    certificate = {'kind': 'observable-closure',
                   'basis': [list(r) for r in basis],
                   'target_coordinates': list(target),
                   'actions': [[list(r) for r in a] for a in actions]}
    return {'status': 'closure', 'certificate': certificate,
            'stats': {'basis_size': len(basis), 'expansions': expansions}}


def shift_model(dimension: int) -> Model:
    """The delayed-error family that attains the D-1 separating bound.

    Ones just above the diagonal, initial state e_D, target e_1. Every output
    before step D-1 is zero and the next one is one, so testing any fixed
    shorter prefix classifies these as correct.
    """
    if dimension < 2:
        raise ValueError('dimension at least two')
    action = tuple(tuple(Q(1) if j == i+1 else Q(0) for j in range(dimension))
                   for i in range(dimension))
    initial = tuple(Q(1) if i == dimension-1 else Q(0) for i in range(dimension))
    output = tuple(Q(1) if i == 0 else Q(0) for i in range(dimension))
    return Model(dimension, initial, output, (action,))


def conservation_gap_model() -> Model:
    """x' = 2x + a, y' = 2y + 2a from (0,0), with the observation 2x - y.

    Its value obeys q' = 2q, not q' = q, so it is not a conserved quantity --
    and it is zero after every input word. One invariant row certifies it, at
    any word length, with no closed form for either coordinate.
    """
    def action(a: int) -> Matrix:
        return ((Q(2), Q(0), Q(a)),
                (Q(0), Q(2), Q(2*a)),
                (Q(0), Q(0), Q(1)))
    initial = (Q(0), Q(0), Q(1))
    output = (Q(2), Q(-1), Q(0))
    return Model(3, initial, output, (action(0), action(1)))
