#!/usr/bin/env python3
"""Independent exact-rational lower bound for the 45-prime order-four saving.

The prime list comes from euler.json and is separately recomputed from the
literal field forms by field_bridge_audit.py. This checker does not call the
manuscript certificate code or floating-point transcendental functions.
"""

from __future__ import annotations

import hashlib
import json
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import factorial
from pathlib import Path


HERE = Path(__file__).resolve().parent
EULER = HERE.parents[2] / "publication/unit-distance-1.0418235/certificates/euler.json"
if not EULER.is_file():
    EULER = HERE / "euler-source.json"
EULER_SHA256 = "4f01e9ae1f0f79f6575955745c1bdf6ce349a03b6990e2e4189a5205426088af"
LOG_GRID = 10**45
X_GRID = 10**40
TERM_GRID = 10**34
TARGET = Q("0.00003724741189544274807446")


def round_up(value: Q, scale: int) -> Q:
    numerator = value.numerator * scale
    quotient = -(-numerator // value.denominator)
    return Q(quotient, scale)


def round_down(value: Q, scale: int) -> Q:
    return Q(value.numerator * scale // value.denominator, scale)


def log_upper(ratio: Q) -> Q:
    """Upper bound from atanh with an explicit positive geometric tail.

    For 1 <= ratio <= 2, q=(ratio-1)/(ratio+1) <= 1/3 and
    log(ratio)=2 sum_{n>=0} q^(2n+1)/(2n+1).
    """
    assert 1 <= ratio <= 2
    q = (ratio - 1) / (ratio + 1)
    count = 35
    partial = 2 * sum((q ** (2 * n + 1) / (2 * n + 1) for n in range(count)), Q(0))
    tail = 2 * q ** (2 * count + 1) / ((2 * count + 1) * (1 - q * q))
    return round_up(partial + tail, LOG_GRID)


def lower_term(p: int, log_two_up: Q) -> Q:
    k = p.bit_length() - 1
    mantissa = Q(p, 1 << k)
    log_p_up = k * log_two_up + log_upper(mantissa)
    t_up = log_p_up / 6000
    assert 0 < t_up < 1

    # The odd Taylor polynomial lies below exp(-t) for 0<t<1.
    exp_lower = sum(((-t_up) ** j / factorial(j) for j in range(10)), Q(0))
    x_lower = round_down(exp_lower / p**2, X_GRID)
    assert 0 < x_lower < 1

    # atanh(x) >= x + x^3/3 + x^5/5 for 0<x<1, and
    # log((1+x)/(1-x))/4 = atanh(x)/2.
    atanh_lower = (x_lower + x_lower**3 / 3 + x_lower**5 / 5) / 2
    return round_down(atanh_lower, TERM_GRID)


def check() -> dict[str, object]:
    if not __debug__:
        raise RuntimeError("Python assertions are required; do not run with -O")
    assert hashlib.sha256(EULER.read_bytes()).hexdigest() == EULER_SHA256
    primes = json.loads(EULER.read_text())["retained_forced_primes"]
    assert len(primes) == 45 and len(set(primes)) == 45
    assert 17 < min(primes) <= max(primes) < 10000
    log_two_up = log_upper(Q(2))
    terms = [lower_term(p, log_two_up) for p in primes]
    lower = sum(terms, Q(0))
    assert lower > TARGET
    with localcontext() as decimal_context:
        decimal_context.prec = 50
        lower_decimal = str(Decimal(lower.numerator) / Decimal(lower.denominator))
    return {
        "status": "pass",
        "euler_sha256": hashlib.sha256(EULER.read_bytes()).hexdigest(),
        "prime_count": len(primes),
        "log_series_terms": 35,
        "exp_polynomial_degree": 9,
        "atanh_polynomial_degree": 5,
        "term_grid": TERM_GRID,
        "saving_lower": str(lower),
        "saving_lower_decimal": lower_decimal,
        "printed_threshold": str(TARGET),
        "strict_gap": str(lower - TARGET),
        "scope": "Exact rational transcendental lower bound conditional on the supplied prime list; field_bridge_audit.py independently verifies that list from literal field forms.",
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
