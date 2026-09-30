#!/usr/bin/env python3
"""Exact-rational replay of the finite local floors and analytic slope debit.

The prime floors and their polynomial masks are read/checked against the
manuscript.  Logarithms are enclosed by rational atanh series after binary
range reduction.  The gamma lower bound is an explicit external input (see
the companion report); this script does not certify Euler's constant.
"""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import re
from decimal import Decimal, localcontext

PROJECT = Path(__file__).resolve().parents[2]
RESEARCH = PROJECT.parent
ANALYTIC = RESEARCH / "publication/unit-distance-1.0418235/sections/analytic.tex"
FIELD = RESEARCH / "publication/unit-distance-1.0418235/sections/retained-field.tex"
if not ANALYTIC.is_file() or not FIELD.is_file():
    ANALYTIC = PROJECT / "docs/manuscript/sections/analytic.tex"
    FIELD = PROJECT / "docs/manuscript/sections/retained-field.tex"
REFERENCE = PROJECT / "verification/external-zeta-20260921/finite-ceiling.json"
OUT = Path(__file__).with_name("debit_check.json")

ANALYTIC_SHA256 = "e088cd4e8664218e023a7c8abbb7fba30839f53eada2b6c60c196c3225ae36db"
FIELD_SHA256 = "dfdd48ba5a2445c94cc8a27b86463a6ece86dc46f57c6eeabff78d5470bdf50d"
REFERENCE_SHA256 = "760198cd7b7163513e72466ce21cec88bd33dd10c2442f2ca092051711b4124c"

B_MASK_HEX = [
    "b401400", "9140a00", "78c1900", "520e700", "2415680", "1c38e00",
    "a138900", "213900", "45f9c00", "1bb80", "800200", "1000",
]
B_MASKS = [int(x, 16) for x in B_MASK_HEX]
RADICANDS = [-1, 2, 3, 5, 7, 11, 13]
EXACT_FOUR = {2, 7, 11, 13, 17, 19, 23, 29, 31}
EXACT_TWO = {3, 5}
RAMIFIED_ODD = {3, 5, 7, 11, 13}
E_TWO = {2: 8, 3: 2, 5: 2, 7: 2, 11: 2, 13: 2}
N_LOG_TERMS = 70
OUTWARD_SCALE = 10**70


def source_check():
    assert sha256(ANALYTIC.read_bytes()).hexdigest() == ANALYTIC_SHA256
    assert sha256(FIELD.read_bytes()).hexdigest() == FIELD_SHA256
    assert sha256(REFERENCE.read_bytes()).hexdigest() == REFERENCE_SHA256
    analytic = ANALYTIC.read_text()
    field = FIELD.read_text()
    assert r"R=\sum_{p\leq10^4}" in analytic
    assert "e_2^0=8" in analytic and "f_p^0=4" in analytic
    assert "first seven coordinates encode $v_i^2$" in field
    assert "lexicographically ordered\n$i<j$." in field
    masks_section = field.split(r"\label{ar:central-masks}", 1)[1]
    masks_table = masks_section.split(r"\begin{array}", 1)[1]
    table = masks_table.split(r"\mathcal B&", 1)[1].split(r"\end{array}", 1)[0]
    masks_in_text = re.findall(r"\\texttt\{([0-9a-f]+)\}", table)
    assert masks_in_text == B_MASK_HEX, masks_in_text
    return {
        "analytic.tex": sha256(ANALYTIC.read_bytes()).hexdigest(),
        "retained-field.tex": sha256(FIELD.read_bytes()).hexdigest(),
        "finite-ceiling.json": sha256(REFERENCE.read_bytes()).hexdigest(),
    }


def primes_to(n):
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            sieve[i * i:n + 1:i] = b"\x00" * (((n - i * i) // i) + 1)
    return [i for i, ok in enumerate(sieve) if ok]


def genus_vector(p):
    assert p not in RAMIFIED_ODD and p != 2
    bits = []
    for a in RADICANDS:
        if a == -1:
            nonresidue = p % 4 == 3
        else:
            residue = pow(a, (p - 1) // 2, p)
            assert residue in (1, p - 1)
            nonresidue = residue == p - 1
        bits.append(int(nonresidue))
    return sum(bit << i for i, bit in enumerate(bits))


def form_value(mask, v):
    # Coordinates: v_i^2 first (equal to v_i in F_2), then v_i v_j,
    # with pairs lexicographically ordered as specified in the manuscript.
    value = 0
    for i in range(7):
        if (mask >> i) & 1:
            value ^= (v >> i) & 1
    k = 7
    for i in range(7):
        for j in range(i + 1, 7):
            if (mask >> k) & 1:
                value ^= ((v >> i) & 1) & ((v >> j) & 1)
            k += 1
    assert k == 28
    return value


def local_floor(p):
    e = E_TWO.get(p, 1)
    if p in EXACT_FOUR:
        f = 4
    elif p in EXACT_TWO:
        f = 2
    else:
        v = genus_vector(p)
        if v == 0:
            f = 1
        elif any(form_value(mask, v) for mask in B_MASKS):
            f = 4
        else:
            f = 2
    return e, f


def log_series_bounds(x, n=N_LOG_TERMS):
    """Rational bounds for log(x), x >= 1, using binary range reduction."""
    x = Fraction(x)
    assert x >= 1
    # Determine k with 1 <= x/2^k < 2 exactly.
    k = x.numerator.bit_length() - x.denominator.bit_length()
    if k >= 0:
        while Fraction(1 << k) > x:
            k -= 1
    else:
        while x < Fraction(1, 1 << (-k)):
            k -= 1
    scale = Fraction(1 << k) if k >= 0 else Fraction(1, 1 << (-k))
    while x / scale >= 2:
        k += 1
        scale *= 2
    while x / scale < 1:
        k -= 1
        scale /= 2
    r = x / scale
    assert 1 <= r < 2

    def unit_bounds(q):
        z = (q - 1) / (q + 1)
        assert 0 <= z < 1
        s = sum((z ** (2 * i + 1)) / (2 * i + 1) for i in range(n)) * 2
        rem = 2 * (z ** (2 * n + 1)) / ((2 * n + 1) * (1 - z * z))
        return s, s + rem

    lo2, hi2 = unit_bounds(Fraction(2))
    lor, hir = unit_bounds(r)
    lo = k * lo2 + lor
    hi = k * hi2 + hir
    return floor_fraction_at_scale(lo), ceil_fraction_at_scale(hi)


def atan_inv_bounds(q, n):
    """Alternating rational series bounds for atan(1/q), n terms."""
    x = Fraction(1, q)
    s = sum(((-1) ** j) * x ** (2 * j + 1) / (2 * j + 1) for j in range(n))
    nxt = x ** (2 * n + 1) / (2 * n + 1)
    return (s, s + nxt) if n % 2 == 0 else (s - nxt, s)


def pi_lower_machin():
    # pi = 16 atan(1/5) - 4 atan(1/239), with exact alternating bounds.
    a5_lo, _ = atan_inv_bounds(5, 80)
    _, a239_hi = atan_inv_bounds(239, 81)
    return floor_fraction_at_scale(16 * a5_lo - 4 * a239_hi)


def dec(x, digits=80):
    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(x.numerator) / Decimal(x.denominator))


def ceil_fraction_at_scale(x):
    """Round a nonnegative rational upward to an exact decimal grid."""
    y = x * OUTWARD_SCALE
    return Fraction(-(-y.numerator // y.denominator), OUTWARD_SCALE)


def floor_fraction_at_scale(x):
    y = x * OUTWARD_SCALE
    return Fraction(y.numerator // y.denominator, OUTWARD_SCALE)


def main():
    if not __debug__:
        raise RuntimeError("Python assertions are required; do not run with -O")
    hashes = source_check()
    ps = primes_to(10_000)
    floors = [[p, *local_floor(p)] for p in ps]
    assert len(ps) == 1229

    finite_r = Fraction(0)
    for p, e, f in floors:
        lp_hi = log_series_bounds(Fraction(p))[1]
        finite_r += ceil_fraction_at_scale(lp_hi / (e * (p ** (2 * f) - 1)))
    log_10000_hi = log_series_bounds(Fraction(10_000))[1]
    tail = ceil_fraction_at_scale((log_10000_hi + 1) / (10_000 * (1 - Fraction(1, 10**8))))
    r_hi = finite_r + tail

    log2_hi = log_series_bounds(Fraction(2))[1]
    log15015_hi = log_series_bounds(Fraction(15015))[1]
    ell_hi = Fraction(9, 4) * log2_hi + Fraction(1, 2) * log15015_hi

    pi_lo = pi_lower_machin()
    log4pi_lo = log_series_bounds(4 * pi_lo)[0]
    # Explicit externally supplied lower enclosure for Euler's constant.
    gamma_lo = Fraction(57721566490153286060651209008240243104215933593992, 10**50)
    slope_hi = (ell_hi - gamma_lo - log4pi_lo) / 4 + r_hi
    debit_hi = slope_hi / 12000

    # A separate relaxed-threshold route uses the theorem already proved in
    # Lean: eulerMascheroniConstant_lower_5767 : gamma >= 5767/10000.
    gamma_lean_lo = Fraction(5767, 10_000)
    slope_lean_gamma_hi = (ell_hi - gamma_lean_lo - log4pi_lo) / 4 + r_hi
    debit_lean_gamma_hi = slope_lean_gamma_hi / 12000
    four_other_allowances = (
        Fraction("0.00044535540710354679437255859375")
        + Fraction("0.041727023150898786")
        - Fraction("0.00003724741189544274807446")
        - Fraction("0.00004201663320373563276702")
    )
    relaxed_total = four_other_allowances + debit_lean_gamma_hi
    selected_cap = Fraction("0.042165819")

    # Mandatory consistency comparison with the pre-existing receipt.  It is
    # not used to derive any floor or bound above.
    reference = json.loads(REFERENCE.read_text())
    ref_floors = reference.get("floors")
    if ref_floors is None:
        raise ValueError("finite-ceiling receipt is missing its floor rows")
    ref_floors = [[int(x) for x in row] for row in ref_floors]
    floors_match = ref_floors == floors
    slope_below_cap = slope_hi < Fraction("0.824453118933538946712643997041")
    debit_below_cap = debit_hi < Fraction("0.00006870442657779491222606")
    relaxed_total_below_cap = relaxed_total < selected_cap
    assert floors_match, "reconstructed floor rows differ from finite-ceiling receipt"
    assert slope_below_cap, "tight slope upper bound exceeds manuscript cap"
    assert debit_below_cap, "tight debit upper bound exceeds manuscript cap"
    assert relaxed_total_below_cap, "coarse-gamma allowance sum exceeds selected H ceiling"

    result = {
        "claim_scope": "finite floor reconstruction and rational upper check for R, slope, debit; not a proof of the prime floors as field-theoretic lower bounds",
        "project_root": str(PROJECT),
        "source_paths": {
            "analytic": str(ANALYTIC),
            "retained_field": str(FIELD),
            "finite_ceiling_reference": str(REFERENCE),
        },
        "source_sha256": hashes,
        "prime_count_through_10000": len(ps),
        "floors_match_external_receipt": floors_match,
        "floors": floors,
        "atanh_terms": N_LOG_TERMS,
        "pi_method": "Machin identity with rational alternating-series enclosure (identity itself is a standard analytic identity)",
        "pi_lower_decimal": dec(pi_lo, 75),
        "gamma_lower_rational_external_input": f"{gamma_lo.numerator}/{gamma_lo.denominator}",
        "gamma_lower_decimal_external_input": dec(gamma_lo, 60),
        "R_finite_upper_rational": f"{finite_r.numerator}/{finite_r.denominator}",
        "R_tail_upper_rational": f"{tail.numerator}/{tail.denominator}",
        "R_upper_rational": f"{r_hi.numerator}/{r_hi.denominator}",
        "R_upper_decimal": dec(r_hi),
        "ell_upper_rational": f"{ell_hi.numerator}/{ell_hi.denominator}",
        "log_4pi_lower_rational": f"{log4pi_lo.numerator}/{log4pi_lo.denominator}",
        "slope_upper_rational": f"{slope_hi.numerator}/{slope_hi.denominator}",
        "slope_upper_decimal": dec(slope_hi),
        "debit_upper_rational": f"{debit_hi.numerator}/{debit_hi.denominator}",
        "debit_upper_decimal": dec(debit_hi),
        "lean_gamma_lower_theorem": "UnitDistance.eulerMascheroniConstant_lower_5767 : gamma >= 5767/10000",
        "slope_upper_with_lean_gamma_rational": f"{slope_lean_gamma_hi.numerator}/{slope_lean_gamma_hi.denominator}",
        "slope_upper_with_lean_gamma_decimal": dec(slope_lean_gamma_hi),
        "debit_upper_with_lean_gamma_rational": f"{debit_lean_gamma_hi.numerator}/{debit_lean_gamma_hi.denominator}",
        "debit_upper_with_lean_gamma_decimal": dec(debit_lean_gamma_hi),
        "four_other_allowances_rational": f"{four_other_allowances.numerator}/{four_other_allowances.denominator}",
        "relaxed_total_rational": f"{relaxed_total.numerator}/{relaxed_total.denominator}",
        "relaxed_total_decimal": dec(relaxed_total),
        "selected_H_ceiling": str(selected_cap),
        "relaxed_total_below_selected_H_ceiling": relaxed_total_below_cap,
        "selected_H_ceiling_slack_rational": f"{(selected_cap-relaxed_total).numerator}/{(selected_cap-relaxed_total).denominator}",
        "selected_H_ceiling_slack_decimal": dec(selected_cap-relaxed_total),
        "manuscript_slope_cap": "0.824453118933538946712643997041",
        "manuscript_debit_cap": "0.00006870442657779491222606",
        "slope_below_cap": slope_below_cap,
        "debit_below_cap": debit_below_cap,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "floors"}, indent=2))


if __name__ == "__main__":
    main()
