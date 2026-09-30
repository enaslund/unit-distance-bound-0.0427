#!/usr/bin/env python3
"""Independent exact-rational assembly of the full stored H7 census bins.

This checks the integer bin table and independently encloses the central
atanh saving from its counts and floor reciprocal sums. It does not enumerate
the primes through 10^12 or call the manuscript producer/replay code.
"""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction as Q
from math import factorial
from pathlib import Path


HERE = Path(__file__).resolve().parent
DATA = HERE / "numerics_h7_census_full.txt"
DATA_SHA256 = "43669734971ae82bdf2980bbacd869a65224fe3cececb121cf2fbc14936813f2"
PREFIX_DATA = HERE / "numerics_h7_census_prefix.txt"
PREFIX_SHA256 = "fafbdaff49c1317d2606df81ca886fea6fb01200b4da7d490e7550bb84b342b3"
LOG_SCALE = 10**50
SUM_SCALE = 10**37
RECIPROCAL_SCALE = 10**30
LOWER_TARGET = Q("0.00004201663320373563276702")
UPPER_TARGET = Q("0.00004201663670363397482805")
SERIES_TERMS = 35


def ceil_div(a: int, b: int) -> int:
    assert a >= 0 and b > 0
    return (a + b - 1) // b


def log_scaled(ratio_num: int, ratio_den: int, upper: bool) -> int:
    """Directed LOG_SCALE-grid enclosure for log(ratio), 1<=ratio<=2.

    The atanh partial sum is positive; the upper side adds the geometric
    remainder using 1/(2n+1) <= 1/(2N+1) for n>=N.
    """
    assert ratio_den <= ratio_num <= 2 * ratio_den
    q_num = ratio_num - ratio_den
    q_den = ratio_num + ratio_den
    assert 0 <= q_num <= q_den // 3
    power_num, power_den = q_num, q_den
    total = 0
    for n in range(SERIES_TERMS):
        numerator = 2 * power_num * LOG_SCALE
        denominator = (2 * n + 1) * power_den
        total += ceil_div(numerator, denominator) if upper else numerator // denominator
        power_num *= q_num * q_num
        power_den *= q_den * q_den
    if upper and q_num:
        numerator = 2 * power_num * LOG_SCALE * q_den * q_den
        denominator = (2 * SERIES_TERMS + 1) * power_den * (q_den * q_den - q_num * q_num)
        total += ceil_div(numerator, denominator)
    return total


LOG_TWO_UPPER = log_scaled(2, 1, True)
LOG_TWO_LOWER = log_scaled(2, 1, False)


def log_integer_scaled(value: int, upper: bool) -> int:
    assert value >= 1
    k = value.bit_length() - 1
    return k * (LOG_TWO_UPPER if upper else LOG_TWO_LOWER) + log_scaled(
        value, 1 << k, upper
    )


def exp_neg_taylor(t: Q, degree: int) -> Q:
    assert 0 <= t < 1
    return sum(((-t) ** j / factorial(j) for j in range(degree + 1)), Q(0))


def read_bins() -> tuple[dict[str, tuple[int, ...]], list[tuple[int, ...]]]:
    raw = DATA.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == DATA_SHA256
    lines = raw.decode().splitlines()
    assert lines[0] == "NONABELIAN_DYADIC_H7_CENSUS_V1" and lines[-1] == "END"
    meta: dict[str, tuple[int, ...]] = {}
    bins = []
    for line in lines[1:-1]:
        key, *values = line.split()
        if key == "field":
            continue
        parsed = tuple(map(int, values))
        if key == "bin":
            assert len(parsed) == 8
            bins.append(parsed)
        else:
            assert key not in meta
            meta[key] = parsed
    return meta, bins


def check() -> dict[str, object]:
    if not __debug__:
        raise RuntimeError("Python assertions are required; do not run with -O")
    meta, bins = read_bins()
    limit = 10**12
    assert meta["limit"] == (limit,)
    assert meta["denominator"] == (RECIPROCAL_SCALE,)
    assert meta["genus_split_count"] == (293772662,)
    assert meta["full_count"] == (293705608,)
    assert meta["completed_count"] == (291485548,)
    assert meta["complement_count"] == (2220060,)
    assert sum(meta["predicate_first_hits"]) == meta["full_count"][0]

    # Reconstruct the full geometric endpoint sequence, including empty bins.
    grid = set()
    lo = 13
    while lo < limit:
        hi = min(limit, max(lo + 1, ceil_div(1001 * lo, 1000)))
        grid.add((lo, hi))
        lo = hi
    assert len(bins) == len(set((b[0], b[1]) for b in bins))
    # Every complete stored prefix bin is byte-for-byte the same integer row
    # in the full table. The separate prefix checker regenerates these rows
    # from primes; omit the terminal bin truncated at the prefix cutoff.
    prefix_raw = PREFIX_DATA.read_bytes()
    assert hashlib.sha256(prefix_raw).hexdigest() == PREFIX_SHA256
    prefix_bins = [tuple(map(int, line.split()[1:]))
                   for line in prefix_raw.decode().splitlines()
                   if line.startswith("bin ") and int(line.split()[2]) < 10**7]
    full_bins = {(b[0], b[1]): b for b in bins}
    assert all(full_bins.get((b[0], b[1])) == b for b in prefix_bins)

    count = first_count = complement_count = 0
    lower_scaled = upper_scaled = 0
    previous_lo = 0
    for lo, hi, n, all_u, first_n, first_u, comp_n, comp_u in bins:
        assert (lo, hi) in grid and lo > previous_lo
        previous_lo = lo
        assert n > 0 and all_u >= 0
        assert 0 <= first_n <= n and 0 <= comp_n <= n
        assert first_n + comp_n == n and first_u + comp_u == all_u
        for bin_n, bin_u in ((n, all_u), (first_n, first_u), (comp_n, comp_u)):
            assert bin_n * (RECIPROCAL_SCALE // hi) <= bin_u
            assert bin_u <= bin_n * (RECIPROCAL_SCALE // (lo + 1))
        count += n
        first_count += first_n
        complement_count += comp_n
        if not comp_n:
            continue

        # h^(-epsilon) = exp(-log(h)/12000), epsilon=1/12000.
        t_hi = Q(log_integer_scaled(hi, True), 12000 * LOG_SCALE)
        exp_lower = exp_neg_taylor(t_hi, 9)  # odd degree: lower
        contribution_lower = exp_lower * Q(comp_u, RECIPROCAL_SCALE)
        scaled_lower = contribution_lower * SUM_SCALE
        lower_scaled += scaled_lower.numerator // scaled_lower.denominator

        # l^(-epsilon) <= P_8(-log(l)/12000) with a lower log input.
        t_lo = Q(log_integer_scaled(lo, False), 12000 * LOG_SCALE)
        exp_upper = exp_neg_taylor(t_lo, 8)  # even degree: upper
        contribution_upper = exp_upper * Q(comp_u + comp_n, RECIPROCAL_SCALE) * Q(lo * lo, lo * lo - 1)
        scaled_upper = contribution_upper * SUM_SCALE
        upper_scaled += ceil_div(scaled_upper.numerator, scaled_upper.denominator)

    assert count == meta["full_count"][0]
    assert first_count == meta["completed_count"][0]
    assert complement_count == meta["complement_count"][0]
    assert meta["genus_split_count"][0] - count == 67054
    lower, upper = Q(lower_scaled, SUM_SCALE), Q(upper_scaled, SUM_SCALE)
    assert LOWER_TARGET < lower <= upper < UPPER_TARGET
    return {
        "status": "pass",
        "data_sha256": DATA_SHA256,
        "prefix_data_sha256": PREFIX_SHA256,
        "matched_complete_prefix_bins": len(prefix_bins),
        "nonempty_bins": len(bins),
        "total_grid_bins": len(grid),
        "full_count": count,
        "completed_count": first_count,
        "complement_count": complement_count,
        "log_series_terms": SERIES_TERMS,
        "lower_exp_degree": 9,
        "upper_exp_degree": 8,
        "sum_rounding_grid": SUM_SCALE,
        "independent_lower": str(lower),
        "independent_upper": str(upper),
        "printed_lower": str(LOWER_TARGET),
        "printed_upper": str(UPPER_TARGET),
        "lower_strict_slack": str(lower - LOWER_TARGET),
        "upper_strict_slack": str(UPPER_TARGET - upper),
        "scope": "Exact rational enclosure of the full stored bin table; does not regenerate the underlying prime census to 10^12.",
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
