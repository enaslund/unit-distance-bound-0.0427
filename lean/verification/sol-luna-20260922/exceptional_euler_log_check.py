#!/usr/bin/env python3
"""Independent rational upper bound for the seven deleted Euler factors.

The factor/exponent table is transcribed from (an:bad-restored) in the
manuscript. The numerical evaluation uses exact rational series bounds only.
"""

from __future__ import annotations

import hashlib
import json
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import factorial
from pathlib import Path


HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
SOURCE = PROJECT.parent / "publication/unit-distance-1.0418235/sections/analytic.tex"
if not SOURCE.is_file():
    SOURCE = PROJECT / "docs/manuscript/sections/analytic.tex"
SOURCE_SHA256 = "e088cd4e8664218e023a7c8abbb7fba30839f53eada2b6c60c196c3225ae36db"
LOG_GRID = 10**45
X_GRID = 10**35
TERM_GRID = 10**25
TARGET = Q("0.041727023150898786")
FACTORS = ((2, 4, 32), (3, 2, 4), (5, 2, 4),
           (7, 4, 8), (11, 4, 8), (13, 4, 8), (17, 4, 4))


def round_up(value: Q, scale: int) -> Q:
    numerator = value.numerator * scale
    return Q(-(-numerator // value.denominator), scale)


def log_lower(ratio: Q) -> Q:
    assert 1 <= ratio <= 2
    q = (ratio - 1) / (ratio + 1)
    return 2 * sum((q ** (2 * n + 1) / (2 * n + 1) for n in range(35)), Q(0))


def factor_upper(p: int, f: int, divisor: int, log_two_low: Q) -> Q:
    k = p.bit_length() - 1
    mantissa = Q(p, 1 << k)
    log_p_low = k * log_two_low + log_lower(mantissa)
    t_low = Q(f, 12000) * log_p_low
    assert 0 < t_low < 1

    # The even Taylor polynomial bounds exp(-t_low) from above.
    exp_upper = sum(((-t_low) ** j / factorial(j) for j in range(9)), Q(0))
    x_upper = round_up(exp_upper / p**f, X_GRID)
    assert 0 < x_upper < 1

    # -log(1-x) is a positive series. Bound its remainder by replacing
    # every denominator n>=26 with 26, then summing the geometric tail.
    count = 25
    partial = sum((x_upper**n / n for n in range(1, count + 1)), Q(0))
    tail = x_upper ** (count + 1) / ((count + 1) * (1 - x_upper))
    return round_up((partial + tail) / divisor, TERM_GRID)


def check() -> dict[str, object]:
    if not __debug__:
        raise RuntimeError("Python assertions are required; do not run with -O")
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA256
    source = SOURCE.read_text()
    assert r"\label{an:bad-restored}" in source
    assert r"\frac{\log(1-2^{-4\sigma})}{32}" in source
    assert r"\sum_{p=3,5}\frac{\log(1-p^{-2\sigma})}{4}" in source
    assert r"\sum_{p=7,11,13}\frac{\log(1-p^{-4\sigma})}{8}" in source
    assert r"\frac{\log(1-17^{-4\sigma})}{4}" in source
    log_two_low = log_lower(Q(2))
    entries = [factor_upper(*row, log_two_low) for row in FACTORS]
    upper = sum(entries, Q(0))
    assert upper < TARGET
    with localcontext() as ctx:
        ctx.prec = 55
        upper_decimal = str(Decimal(upper.numerator) / Decimal(upper.denominator))
    return {
        "status": "pass",
        "analytic_source_sha256": SOURCE_SHA256,
        "factors": [list(row) for row in FACTORS],
        "log_series_terms": 35,
        "exp_polynomial_degree": 8,
        "negative_log_series_terms": 25,
        "factor_rounding_grid": TERM_GRID,
        "exceptional_upper": str(upper),
        "exceptional_upper_decimal": upper_decimal,
        "printed_allowance": str(TARGET),
        "strict_slack": str(TARGET - upper),
        "scope": "Exact rational upper enclosure for the seven displayed exceptional factors; local residue indices are mathematical inputs from the manuscript, not proved here.",
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
