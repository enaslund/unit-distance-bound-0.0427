"""Interval bounds shared by the Q(sqrt 241) numerical certificates."""
import math

import env241  # noqa: F401 (path setup, PYLIB)
from flint import arb


def outward_float_bounds(value):
    """Finite JSON-number endpoints enclosing an Arb ball, rounded outward.

    Moving one float beyond each rounded endpoint also allows for the
    shortest-decimal serialization used by JSON. Check those actual decimal
    strings in Arb before returning them; insufficient precision fails closed.
    """
    if not value.is_finite():
        raise ValueError("Cannot export a nonfinite enclosure")
    if value.is_zero():
        return [0.0, 0.0]
    lo = math.nextafter(float(value.lower()), -math.inf)
    hi = math.nextafter(float(value.upper()), math.inf)
    if not (math.isfinite(lo) and math.isfinite(hi)):
        raise ValueError("Enclosure exceeds the finite float range")
    if not (arb(repr(lo)) <= value.lower() and value.upper() <= arb(repr(hi))):
        raise ArithmeticError("Decimal endpoints do not enclose the Arb ball")
    return [lo, hi]


def logderiv_tail_bound(X):
    """Upper bound for sum_{n>X} log(n)/(n^2-1), using only Arb arithmetic.

    For integer X >= 2, replace 1/(1-n^-2) by 1/(1-X^-2) and bound
    the decreasing sum of log(n)/n^2 by its integral from X to infinity.
    """
    if not isinstance(X, int) or X < 2:
        raise ValueError("The tail cutoff must be an integer at least 2")
    x = arb(X)
    return (x.log() + 1) / (x * (1 - 1 / x**2))


def require_strict_upper_bound(enclosure, ceiling):
    """Reject unless the complete enclosure is strictly below the ceiling."""
    value, limit = arb(enclosure), arb(ceiling)
    if not (value.is_finite() and limit.is_finite() and value < limit):
        raise ValueError(f"Uncertified upper bound: {value} is not strictly below {limit}")
