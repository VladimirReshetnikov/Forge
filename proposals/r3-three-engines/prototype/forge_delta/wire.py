"""Canonical exact wire primitives; deliberately shared, not a verified decoder."""
from fractions import Fraction
from typing import Any

MAX_BITS = 100_000

def q(x: Any) -> Fraction:
    if isinstance(x, bool) or isinstance(x, float):
        raise ValueError('Booleans and floating-point numbers are not rationals')
    if not isinstance(x, (str, int, Fraction)):
        raise ValueError('Expected an exact rational')
    r = Fraction(x)
    if isinstance(x, str) and str(r) != x:
        raise ValueError('Noncanonical rational')
    if max(abs(r.numerator).bit_length(), r.denominator.bit_length()) > MAX_BITS:
        raise ValueError('Rational bit budget exceeded')
    return r

def qs(x: Any) -> str:
    return str(q(x))

def require(condition: bool, message: str = 'Invalid certificate') -> None:
    if not condition:
        raise ValueError(message)
