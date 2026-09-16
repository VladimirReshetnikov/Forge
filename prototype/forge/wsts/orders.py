# PROVENANCE: s1, s3 and s4 each shipped their own well-quasi-order, antichain
# and predecessor routine. They are the same three things. This module states
# each of them once; the model families in nets.py supply only what genuinely
# differs, which is the predecessor RULE, not the order machinery around it.
"""Well-quasi-orders, antichains, and the predecessor of an upward-closed set.

A well-quasi-order here is a reflexive transitive relation in which every
infinite sequence has an increasing pair. That is exactly the property the
backward search needs: it guarantees the antichain of minimal elements stops
growing, so the search terminates. It does NOT bound how long that takes, and
nothing in this module claims a complexity result. Exhausting a budget is an
inconclusive refusal, never a proof of safety.

Two orders are enough for the four lanes merged here:

  Dickson   componentwise order on N^d.       Dickson's lemma.
  Higman    subsequence order on words over   Higman's lemma.
            a finite alphabet, applied
            channelwise to a tuple of words.

Both are decidable in the obvious way, and both refuse to compare elements of
different shapes rather than letting `zip` silently truncate a dimension --- a
truncated comparison would make the antichain below accept a dominated element
and quietly destroy minimality.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Callable, Iterable, Iterator, Sequence

Vector = tuple[int, ...]


def natural(x: Any, context: str = 'value') -> int:
    """Accept a nonnegative int. Reject bool: in Python `True == 1` is true."""
    if type(x) is not int or x < 0:
        raise ValueError(f'{context}: expected a nonnegative integer (bool is not one)')
    return x


def vector(xs: Any, d: int, context: str = 'vector') -> Vector:
    if not isinstance(xs, (list, tuple)) or len(xs) != d:
        raise ValueError(f'{context}: dimension mismatch')
    return tuple(natural(x, context) for x in xs)


# --------------------------------------------------------------------------
# Dickson: N^d under the componentwise order.
# --------------------------------------------------------------------------
def dickson_leq(a: Sequence[int], b: Sequence[int]) -> bool:
    if len(a) != len(b):
        raise ValueError('dimension mismatch')
    return all(a[i] <= b[i] for i in range(len(a)))


# --------------------------------------------------------------------------
# Higman: the subsequence order on words.
# --------------------------------------------------------------------------
def subsequence(s: str, t: str) -> bool:
    """True when s embeds into t as a (not necessarily contiguous) subsequence.

    Deliberately the dynamic program rather than the one-pass greedy scan. The
    greedy scan is correct and is what a producer would use; running a second
    algorithm here means a defect in either one is visible as a disagreement
    instead of being confirmed by its own twin. See s4, which made the same
    choice for the same reason.
    """
    n = len(s)
    if n > len(t):
        return False
    # reached[k]: the first k symbols of s embed into the prefix of t so far.
    reached = [False] * (n + 1)
    reached[0] = True
    for letter in t:
        for k in range(n, 0, -1):
            if letter == s[k - 1] and reached[k - 1]:
                reached[k] = True
    return reached[n]


def higman_leq(a: Sequence[str], b: Sequence[str]) -> bool:
    if len(a) != len(b):
        raise ValueError('channel count mismatch')
    return all(subsequence(a[i], b[i]) for i in range(len(a)))


# --------------------------------------------------------------------------
# Antichains.
# --------------------------------------------------------------------------
class Antichain:
    """The minimal elements of an upward-closed set, kept minimal on insertion.

    `add` returns True when the element was genuinely new information --- that
    is, when nothing already present was below it. Elements strictly above the
    newcomer are discarded, because their upward closures are contained in its.

    This is the search-side structure. Its `add` is where all four proposals'
    searches spent their time, and discarding is what keeps the basis small.
    A CHECKER must never discard anything: it is handed a finished antichain
    and verifies minimality directly, which `canonical` below does.
    """

    __slots__ = ('leq', 'elements')

    def __init__(self, leq: Callable[[Any, Any], bool],
                 elements: Iterable[Any] = ()) -> None:
        self.leq = leq
        self.elements: list[Any] = []
        for element in elements:
            self.add(element)

    def __len__(self) -> int:
        return len(self.elements)

    def __iter__(self) -> Iterator[Any]:
        return iter(self.elements)

    def __contains__(self, x: Any) -> bool:
        """Membership in the UPWARD CLOSURE, which is the set this represents."""
        return any(self.leq(e, x) for e in self.elements)

    def add(self, x: Any) -> bool:
        if x in self:
            return False
        self.elements = [e for e in self.elements if not self.leq(x, e)]
        self.elements.append(x)
        return True

    def covers(self, x: Any) -> Any | None:
        """Return a witness element below x, or None. Used to build receipts."""
        for e in self.elements:
            if self.leq(e, x):
                return e
        return None


def canonical(elements: Sequence[Any], leq: Callable[[Any, Any], bool]) -> bool:
    """Is this list sorted, duplicate-free, and pairwise incomparable?

    The sortedness requirement is not mathematics; it is what makes two
    certificates for the same basis byte-identical, so that a diff of two runs
    means something. The incomparability requirement IS mathematics: without
    it a "minimal" basis can contain a redundant element, and a checker that
    accepted one would be certifying a weaker statement than it reports.
    """
    if list(elements) != sorted(elements):
        return False
    for i in range(len(elements)):
        for j in range(i):
            if leq(elements[i], elements[j]) or leq(elements[j], elements[i]):
                return False
    return True


# --------------------------------------------------------------------------
# The predecessor of an upward-closed set, for ordinary vector additions.
# --------------------------------------------------------------------------
def predecessor(consume: Sequence[int], produce: Sequence[int],
                target: Sequence[int]) -> Vector:
    """The least marking from which firing this transition covers `target`.

    Firing needs `consume`, then returns `produce`, so from x the successor is
    x - consume + produce, and covering `target` needs

        x - consume + produce >= target   and   x >= consume,

    whose componentwise least solution is consume + max(0, target - produce).
    This is a least element, not merely some sufficient one, which is why the
    upward closure of the result is exactly the predecessor set and the
    backward search stays complete.

    s1's model, s1's checker and s3's search each wrote this expression out.
    They agree. It is written once here.
    """
    if not (len(consume) == len(produce) == len(target)):
        raise ValueError('dimension mismatch')
    return tuple(consume[i] + max(0, target[i] - produce[i])
                 for i in range(len(target)))


@dataclass(frozen=True)
class Budget:
    """Operational refusal thresholds. Exceeding one yields UNKNOWN.

    Kept as data rather than constants so a caller can say what it is willing
    to spend without editing the search. None of these numbers has any
    mathematical content.
    """
    admissions: int = 20_000
    predecessors: int = 200_000
    basis: int = 5_000
