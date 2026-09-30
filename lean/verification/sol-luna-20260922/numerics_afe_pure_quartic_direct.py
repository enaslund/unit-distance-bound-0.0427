#!/usr/bin/env python3
"""Direct pointwise Arb AFE replay for one H7 pure-quartic factor.

This is deliberately independent of the manuscript's degree-40 sparse-bin
moment summation: it reconstructs exact Hecke coefficients from the defining
local residue rules, then evaluates the four-Gamma Mellin kernel at each
nonzero coefficient by its pinned residue-series routine.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from fractions import Fraction
from pathlib import Path

from flint import arb, acb, ctx

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PUB = REPO / "publication"
RESEARCH = PUB / "nonabelian-dyadic-lower-bound/research"
KERNEL_PATH = PUB / "six-dimensional-lower-bound/research/h7-analytic-kernel.py"
AFE_HELPER_PATH = RESEARCH / "h7-pure-quartic-afe.py"
COEFF_CHECKER = HERE / "numerics_hecke_coeff_check.py"
COEFF_FIXTURE = HERE / "numerics_hecke_coeff_fixture.json"
ARITHMETIC = RESEARCH / "h7-pure-arithmetic.json"
MOMENTS = RESEARCH / "h7-pure-moments.json"
AFE_TABLE = RESEARCH / "h7-pure-euler-12000.json"

PINS = {
    "h7-analytic-kernel.py": "2b47df974b40453a1440df740bb011648c28a3297d4fc598eaa70d0121a34150",
    "h7-pure-quartic-afe.py": "0dc7bbafd9fe81660cb74b4f1a5ca0fefed6a622dd31c7f2241f7feae0919342",
    "numerics_hecke_coeff_check.py": "3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329",
    "numerics_hecke_coeff_fixture.json": "db0e2050cf3e9a3d1f0b79f4481b55609b52fb071a2ade4c93acfc21e864a1ae",
    "h7-pure-arithmetic.json": "e1d892ba20f90bf6ea15e52f710ead0b8806a6db50d95792a76ebe2552183948",
    "h7-pure-moments.json": "c999ec7882f758e72f683fc3572406ed0d325ff674958e23a0349f322ecd84bf",
    "h7-pure-euler-12000.json": "441ecbc24ae113807de6de5b2e911c356c98c6df6947bdac7e94233cb49a2d3e",
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def endpoint_fraction(record: dict[str, str]) -> Fraction:
    value = Fraction(int(record["mantissa"]))
    exponent = int(record["exponent"])
    return value * (2**exponent) if exponent >= 0 else value / (2 ** (-exponent))


def source_interval(record: dict[str, object]) -> tuple[Fraction, Fraction]:
    return endpoint_fraction(record["lower"]), endpoint_fraction(record["upper"])


def arb_endpoint_fraction(value: arb) -> Fraction:
    mantissa, exponent = value.man_exp()
    exact = Fraction(int(mantissa))
    return exact * (2**int(exponent)) if exponent >= 0 else exact / (2 ** (-int(exponent)))


def enc(value: arb) -> dict[str, object]:
    def one(x: arb) -> dict[str, object]:
        m, e = x.man_exp()
        return {"mantissa": str(m), "exponent": int(e)}
    return {"lower": one(value.lower()), "upper": one(value.upper()),
            "display": value.str(35, radius=True)}


def overlap(value: arb, record: dict[str, object]) -> bool:
    lo, hi = source_interval(record)
    return arb_endpoint_fraction(value.lower()) <= hi and lo <= arb_endpoint_fraction(value.upper())


def contained_in_source_center_plus_error(
    value: arb, centre_record: dict[str, object], error_record: dict[str, object]
) -> bool:
    centre_lo, centre_hi = source_interval(centre_record)
    _error_lo, error_hi = source_interval(error_record)
    return (centre_lo - error_hi <= arb_endpoint_fraction(value.lower()) and
            arb_endpoint_fraction(value.upper()) <= centre_hi + error_hi)


def main() -> None:
    if not __debug__:
        raise RuntimeError("Python assertions are required")
    paths = {
        "h7-analytic-kernel.py": KERNEL_PATH,
        "h7-pure-quartic-afe.py": AFE_HELPER_PATH,
        "numerics_hecke_coeff_check.py": COEFF_CHECKER,
        "numerics_hecke_coeff_fixture.json": COEFF_FIXTURE,
        "h7-pure-arithmetic.json": ARITHMETIC,
        "h7-pure-moments.json": MOMENTS,
        "h7-pure-euler-12000.json": AFE_TABLE,
    }
    for name, path in paths.items():
        actual = sha(path)
        if actual != PINS[name]:
            raise AssertionError(f"{name} hash mismatch: {actual}")

    ctx.prec = 512
    kernel = load_module("pure_quartic_kernel_direct", KERNEL_PATH)
    coeff = load_module("independent_hecke_coeff_rules", COEFF_CHECKER)
    row, sector, used_fixture = coeff.selected_inputs()
    assert used_fixture and sector["mask"] == 1920

    table = json.loads(AFE_TABLE.read_text())
    assert table["sigma"] == "12001/12000" and table["N"] == 1_921_920
    printed = next(r for r in table["rows"] if r["twist"] == -1)
    arithmetic = json.loads(ARITHMETIC.read_text())
    source_sector = next(s for s in arithmetic["sectors"] if s["mask"] == 1920)
    source_row = next(r for r in source_sector["rows"] if r["twist"] == -1)
    for key in ("twist", "conductor", "bad_euler_denominators", "first128_complex_coefficients"):
        if row.get(key) != source_row.get(key):
            raise AssertionError(f"compact coefficient fixture differs from arithmetic source at {key}")
    for key in ("twist", "conductor", "gamma", "root_number"):
        if source_row.get(key) != printed.get(key):
            raise AssertionError(f"arithmetic source and AFE row differ at {key}")
    assert printed["gamma"] == [1, 1, 1, 1] and printed["root_number"] == 1
    assert source_row["parity"] == 1 and source_row["gamma"] == [1, 1, 1, 1]
    N = printed["N"]

    # The residue-character/local-Euler implementation in the separate
    # coefficient checker is generalized to the pinned full AFE cutoff.
    coeff.LIMIT = N
    coefficients = coeff.first128(row, sector)
    if len(coefficients) != N:
        raise AssertionError(f"coefficient generator returned {len(coefficients)} terms")
    if coefficients[:128] != row["first128_complex_coefficients"]:
        raise AssertionError("independent coefficient prefix no longer matches the pinned row")
    nonzero = sum(bool(re or im) for re, im in coefficients)
    if nonzero != printed["nonzero_coefficients"]:
        raise AssertionError(f"nonzero count {nonzero} differs from AFE source")
    if any(im for re, im in coefficients):
        raise AssertionError("selected pure-quartic row unexpectedly has nonreal coefficients")
    stored_moments = json.loads(MOMENTS.read_text())
    moment_row = next(r for r in stored_moments["rows"] if r["twist"] == -1)
    if moment_row["N"] != N or len(moment_row["bins"]) == 0:
        raise AssertionError("pinned exact-moment row has wrong cutoff or no bins")
    for bin_record in moment_row["bins"]:
        observed_count = 0
        observed_mass = 0
        observed_sum = 0
        for n in range(bin_record["lo"], bin_record["hi"] + 1):
            re, im = coefficients[n - 1]
            if im:
                raise AssertionError(f"nonreal coefficient at n={n}")
            if re:
                observed_count += 1
                observed_mass += abs(re) * n
                observed_sum += re * n
        if (observed_count != bin_record["count"] or
                observed_mass != bin_record["mass"] or
                observed_sum != bin_record["moments"][0]):
            raise AssertionError(f"independent coefficients disagree with pinned moments in bin {bin_record['index']}")

    s = kernel.q(Fraction(12001, 12000))
    Q = int(printed["conductor"])
    parity = 1
    t = arb.pi()**2 / arb(Q).sqrt()
    b = (s + parity) / 2
    dual = (1 - s + parity) / 2
    F = t**(s + parity) / b.gamma()**4
    A = arb(0)
    B = arb(0)
    for n, (re, _im) in enumerate(coefficients, start=1):
        if not re:
            continue
        x = (t * n)**2
        weight = int(re) * n
        A += weight * kernel.kernels(x, b)[1]
        B += weight * kernel.kernels(x, dual)[1]
    A *= F
    B *= F
    # The stored A/B fields are the centre polynomial sums from the source's
    # bin-Taylor evaluation. Its separate one-side remainder is the justified
    # allowance for comparing those centres with the direct pointwise sums.
    interpolation = printed["one_side_interpolation_error"]
    if not contained_in_source_center_plus_error(A, printed["A_finite"], interpolation):
        raise AssertionError(f"direct primary sum {enc(A)} escapes printed centre plus interpolation error")
    if not contained_in_source_center_plus_error(B, printed["B_finite"], interpolation):
        raise AssertionError(f"direct dual sum {enc(B)} escapes printed centre plus interpolation error")

    # The row's finite-image degree-four Euler data gives |a_n| <= d_4(n),
    # hence sum |a_n| n^-beta <= zeta(beta)^4. The positive Mellin kernel
    # bounds each omitted side by F*n0^(beta+1)*K_(beta+1)/2(t^2*n0^2)*mass.
    candidates = []
    n0 = N + 1
    for beta in map(Fraction, ("5/4", "3/2", "2", "3", "4")):
        bb = kernel.q(beta)
        C = (bb + parity) / 2
        assert C >= b and C >= dual
        tail = F * arb(n0)**(bb + parity) * kernel.kernels((t*n0)**2, C)[1] * bb.zeta()**4
        candidates.append((tail, beta))
    tail, beta = min(candidates, key=lambda pair: pair[0].upper())
    modulus_upper = abs(A + B).upper() + 2 * tail.upper()
    if not modulus_upper > 0:
        raise AssertionError("invalid modulus upper bound")

    log_bad = arb(0)
    for ptext, polynomial in source_row["bad_euler_denominators"].items():
        if any(int(im) != 0 for _re, im in polynomial):
            raise AssertionError(f"bad factor at p={ptext} is nonreal")
        z = arb(int(ptext))**(-s)
        den = sum((int(re) * z**j for j, (re, _im) in enumerate(polynomial)), arb(0))
        if not den > 0:
            raise AssertionError(f"bad Euler denominator at p={ptext} is not positive")
        log_bad += den.log()
    if not overlap(log_bad, printed["BAD7_log_removal"]):
        raise AssertionError("direct bad-prime removal does not overlap the printed allowance interval")
    log_upper = (modulus_upper.log() + log_bad).upper()
    printed_interval = source_interval(printed["log_L_S_upper"])
    passed = arb_endpoint_fraction(log_upper) <= printed_interval[1]
    result = {
        "status": "PASS direct pointwise pure-quartic AFE row bound" if passed else "direct upper exceeds printed row allowance",
        "sigma": str(Fraction(12001, 12000)), "sector": 1920, "twist": -1,
        "degree": 4, "conductor": Q, "gamma": printed["gamma"], "root_number": 1,
        "N": N, "coefficients_generated": len(coefficients), "nonzero_coefficients": nonzero,
        "precision_bits": ctx.prec, "python_flint_version": __import__("flint").__version__,
        "flint_version": __import__("flint").__FLINT_VERSION__,
        "A_finite": enc(A), "B_finite": enc(B),
        "A_direct_within_source_center_plus_interpolation_error": True,
        "B_direct_within_source_center_plus_interpolation_error": True,
        "bad_log_overlaps_printed": True,
        "tail_rankin_beta": str(beta), "one_side_tail_upper": enc(tail.upper()),
        "L_modulus_upper": enc(modulus_upper), "bad_log_removal": enc(log_bad),
        "log_L_S_upper": enc(log_upper), "printed_log_L_S_upper": printed["log_L_S_upper"],
        "comparison_below_printed_allowance": passed,
        "source_sha256": PINS,
        "coefficient_method": "independent residue-character and local Euler recurrence; first 128 checked against pinned row",
        "kernel_method": "direct pointwise four-Gamma Mellin residue series at each nonzero coefficient; no degree-40 moment/bin interpolation",
        "conditional_assumptions": [
            "the pinned conductor, gamma signature, and unit root number describe an entire completed degree-four L-function with the stated functional equation",
            "the finite-image degree-four local Euler data imply |a_n| <= d_4(n) for all n, so the absolute Rankin mass is bounded by zeta(beta)^4",
            "the listed bad-prime denominators are the row's complete removed local factors",
        ],
        "scope": "Independent conditional numerical cross-check of one row; not a proof of the global hypothesis H or of the representation-to-row identity.",
    }
    print(json.dumps(result, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
