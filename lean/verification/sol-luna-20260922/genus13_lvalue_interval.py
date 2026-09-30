#!/usr/bin/env python3
"""Rational enclosure for L(χ_13, 12001/12000) from its period-13 series.

This deliberately avoids the manuscript completion/AFE machinery. The only
analytic tail input is summation by parts with period partial sums bounded by
2. Finite term intervals use exact rational atanh and alternating-exp series.
"""

from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
SCALE = 10**40
N = 13_000  # multiple of 13, so the character partial sum at N is zero
LOG_TERMS = 12
EXP_LOWER_DEGREE = 7  # odd Taylor truncation is a lower bound for exp(-x)
EXP_UPPER_DEGREE = 8  # even Taylor truncation is an upper bound
FIXTURE_PATH = Path(__file__).with_name("genus13_lvalue_interval_fixture.json")
FIXTURE_SHA256 = "915c0020aa13ee97ce3544565d214e4c320e023e6fce4e7bfddd21fc6a6ad212"
PERIOD = (1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, 1, 0)
PINNED_SOURCE_HASHES = {
    "lean-formalization/UnitDistance/GenusDirichletConductorsRun20260920.lean":
        "da1f113fb627a0e64651d1b5998f453f7d0e452771ea0a1f18ada752ca9b3a77",
    "lean-formalization/UnitDistance/GenusLunaRun20260922ConductorThirteen.lean":
        "110cc2883052d0cfa0a18f048c809a91154365cf31039e34a0c8c04e83694950",
}


def floor_q(x: F) -> int:
    return x.numerator // x.denominator


def ceil_q(x: F) -> int:
    return -floor_q(-x)


def fixed_decimal(n: int, places: int) -> str:
    sign = "-" if n < 0 else ""
    whole, fractional = divmod(abs(n), 10**places)
    return f"{sign}{whole}.{fractional:0{places}d}"


def atanh_log_bounds(y: F) -> tuple[F, F]:
    """Enclose log(y), 1 <= y <= 2, using 2 atanh((y-1)/(y+1))."""
    t = (y - 1) / (y + 1)
    total = F(0)
    power = t
    for j in range(LOG_TERMS):
        total += 2 * power / (2 * j + 1)
        power *= t * t
    # The omitted denominators are at least 2K+1; sum the geometric powers.
    remainder = 2 * power / ((2 * LOG_TERMS + 1) * (1 - t * t))
    return total, total + remainder


def log_integer_bounds(n: int) -> tuple[F, F]:
    if n == 1:
        return F(0), F(0)
    k = n.bit_length() - 1
    mantissa = F(n, 1 << k)
    ml, mu = atanh_log_bounds(mantissa)
    l2, u2 = atanh_log_bounds(F(2))
    return ml + k * l2, mu + k * u2


def exp_minus_taylor(x: F, degree: int) -> F:
    total = F(0)
    term = F(1)
    for k in range(degree + 1):
        if k:
            term *= -x / k
        total += term
    return total


def legendre13(n: int) -> int:
    r = n % 13
    if r == 0:
        return 0
    residues = {pow(a, 2, 13) for a in range(1, 13)}
    return 1 if r in residues else -1


def main() -> None:
    fixture_bytes = FIXTURE_PATH.read_bytes()
    assert sha256(fixture_bytes).hexdigest() == FIXTURE_SHA256, "source fixture hash changed"
    fixture = json.loads(fixture_bytes)
    assert tuple(fixture["period_coefficients"]) == PERIOD
    assert fixture["source_sha256"] == PINNED_SOURCE_HASHES

    present = {name: (ROOT / name).is_file() for name in PINNED_SOURCE_HASHES}
    assert all(present.values()) or not any(present.values()), "partial source checkout"
    source_binding_mode = "compact fixture only; Lean source files absent"
    if all(present.values()):
        for relative, expected in PINNED_SOURCE_HASHES.items():
            actual = sha256((ROOT / relative).read_bytes()).hexdigest()
            assert actual == expected, f"pinned source hash changed: {relative}"
        conductors = (ROOT / list(PINNED_SOURCE_HASHES)[0]).read_text()
        row = (ROOT / list(PINNED_SOURCE_HASHES)[1]).read_text()
        assert "abbrev commonChi13 := commonPrimeQuadraticCharacter 13" in conductors
        assert "primeQuadraticCharacter q hq" in conductors
        assert "conductorThirteen_primitive_apply" in row
        assert "primeQuadraticCharacter 13" in row
        source_binding_mode = "Lean sources present; both source SHA-256 pins and bindings matched"

    literal_period = tuple(legendre13(n) for n in range(1, 14))
    assert literal_period == PERIOD
    # Period sum zero; partial sums in the literal period stay in [-2, 2].
    running = 0
    partials = []
    for value in literal_period:
        running += value
        partials.append(running)
    assert running == 0 and max(map(abs, partials)) == 2

    lower_scaled = 0
    upper_scaled = 0
    sigma_delta = 12_000  # s = 1 + 1/12000
    for n in range(1, N + 1):
        chi = literal_period[(n - 1) % 13]
        if not chi:
            continue
        log_lo, log_hi = log_integer_bounds(n)
        x_lo, x_hi = log_lo / sigma_delta, log_hi / sigma_delta
        assert 0 <= x_lo <= x_hi < 1
        lo = exp_minus_taylor(x_hi, EXP_LOWER_DEGREE) / n
        hi = exp_minus_taylor(x_lo, EXP_UPPER_DEGREE) / n
        assert lo <= hi
        term_lo, term_hi = floor_q(SCALE * lo), ceil_q(SCALE * hi)
        if chi == 1:
            lower_scaled += term_lo
            upper_scaled += term_hi
        else:
            lower_scaled -= term_hi
            upper_scaled -= term_lo

    # Since N is a period endpoint, the shifted character partial sums have
    # absolute value at most 2. Summation by parts bounds the infinite tail by
    # 2 (N+1)^(-s) < 2/(N+1), using s > 1.
    tail_scaled = ceil_q(SCALE * F(2, N + 1))
    lower_scaled -= tail_scaled
    upper_scaled += tail_scaled
    assert lower_scaled <= upper_scaled

    print(f"source binding: {source_binding_mode}")
    print(f"fixture SHA-256: {FIXTURE_SHA256}")
    print(f"pinned source hashes: {PINNED_SOURCE_HASHES}")
    print(f"period coefficients: {literal_period}")
    print(f"period sum: {sum(literal_period)}; maximum absolute partial sum: 2")
    print(f"s: 12001/12000; finite cutoff N: {N}; exact tail radius: 2/{N+1}")
    print(f"lower rational: {lower_scaled}/{SCALE}")
    print(f"upper rational: {upper_scaled}/{SCALE}")
    display_scale = 10**15
    lower_display = floor_q(F(lower_scaled, SCALE) * display_scale)
    upper_display = ceil_q(F(upper_scaled, SCALE) * display_scale)
    print(f"lower decimal (outward): {fixed_decimal(lower_display, 15)}")
    print(f"upper decimal (outward): {fixed_decimal(upper_display, 15)}")
    print("scope: primitive quadratic Dirichlet L(χ_13,s), real s; not an AFE completion")


if __name__ == "__main__":
    main()
