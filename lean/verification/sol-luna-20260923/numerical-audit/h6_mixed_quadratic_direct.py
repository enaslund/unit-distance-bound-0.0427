#!/usr/bin/env python3
"""Hash-pinned direct pointwise replay for H6 mixed-quadratic mask 1586, twist +1.

This adds an untested row (Q=240240, N=3922) to the prior twist -1 check.
It reuses the pinned nonpositive-afe.py quadratic SplitKernels and python-flint
backend; the direct coefficient contraction is independent of stored bin
moments, but this is not a new analytic kernel or interval backend.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PUB = REPO / "publication"
RESEARCH = PUB / "nonabelian-dyadic-lower-bound/research"
AFE_SOURCE = PUB / "five-prime-lower-bound/research/nonpositive-afe.py"
COEFF_SOURCE = REPO / "lean-formalization/verification/sol-luna-20260922/numerics_hecke_coeff_check.py"
ARITH = RESEARCH / "h6-low-degree-arithmetic.json"
MOMENTS = RESEARCH / "h6-low-degree-moments-1586.json"
EVALUATION = RESEARCH / "h6-low-degree-euler-6000.json"
LOW_EULER_SOURCE = RESEARCH / "h6-low-degree-euler.py"
LOW_ARITH_SOURCE = RESEARCH / "h6-low-degree-arithmetic.py"
HEECKE_AFE = PUB / "unit-distance-lower-bound/certificates/hecke_afe.py"
EXACT_GROUP = PUB / "unit-distance-lower-bound/certificates/exact_group.py"
OUTPUT = HERE / "h6_mixed_quadratic_direct.json"

PINS = {
    "h6-low-degree-arithmetic.json": (ARITH, "b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771"),
    "h6-low-degree-moments-1586.json": (MOMENTS, "a7e65537a05389f11115a8cf64c186ead6b1dc4973a8c5f862f31a34fdeb40f1"),
    "h6-low-degree-euler-6000.json": (EVALUATION, "bd9c19c7b128a17fd1ea84afae062f812bb2915b4fe2dfea813bfb074496d459"),
    "h6-low-degree-euler.py": (LOW_EULER_SOURCE, "9fdee8fe5bd9fcbc90c9b28ccbdd0ec5066d49b8b52757ee3f20cc89af707f38"),
    "h6-low-degree-arithmetic.py": (LOW_ARITH_SOURCE, "09cf2aae4e0f67bf3dee34289fd767635b0499801e81d787950f48b53599c14f"),
    "numerics_hecke_coeff_check.py": (COEFF_SOURCE, "3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329"),
    "nonpositive-afe.py": (AFE_SOURCE, "8d6b82b12f7de4a3d53feccde8aaffe0d0fbdf4b623c1447af6ea68ed399cba7"),
    "hecke_afe.py": (HEECKE_AFE, "21e5c3187ff9e98e4fb42bcb39b6c3ec6ece47ef5eb2807ea2c2fd8daca4b7bd"),
    "exact_group.py": (EXACT_GROUP, "b336d10f1beb4fb117685c899e938508e1aaf83def27b6b7a072ed6b12bf1b35"),
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def endpoint_fraction(value) -> Fraction:
    mantissa, exponent = value.man_exp()
    exact = Fraction(int(mantissa))
    return exact * (2 ** int(exponent)) if exponent >= 0 else exact / (2 ** (-int(exponent)))


def source_endpoint(record: dict) -> Fraction:
    value = Fraction(int(record["mantissa"]))
    exponent = int(record["exponent"])
    return value * (2 ** exponent) if exponent >= 0 else value / (2 ** (-exponent))


def source_interval(record: dict) -> tuple[Fraction, Fraction]:
    return source_endpoint(record["lower"]), source_endpoint(record["upper"])


def encode_arb(value) -> dict:
    def one(endpoint):
        m, e = endpoint.man_exp()
        return {"mantissa": str(m), "exponent": int(e)}
    return {"lower": one(value.lower()), "upper": one(value.upper()),
            "display": value.str(36, radius=True)}


def overlap(value, record: dict) -> bool:
    lo, hi = source_interval(record)
    return endpoint_fraction(value.lower()) <= hi and lo <= endpoint_fraction(value.upper())


def contained_real_in_center_plus_error(value, center_record: dict, error_record: dict) -> bool:
    lo, hi = source_interval(center_record)
    _err_lo, err_hi = source_interval(error_record)
    return lo - err_hi <= endpoint_fraction(value.lower()) and endpoint_fraction(value.upper()) <= hi + err_hi


def contained_complex_in_center_plus_error(value, center_record: dict, error_record: dict) -> bool:
    return (contained_real_in_center_plus_error(value.real, center_record["real"], error_record)
            and contained_real_in_center_plus_error(value.imag, center_record["imag"], error_record))


def check_exact_bins(coefficients: list[list[int]], bins: list[dict], N: int) -> None:
    ordered = sorted(bins, key=lambda b: int(b["lo"]))
    assert ordered and int(ordered[0]["lo"]) == 1 and int(ordered[-1]["hi"]) == N
    assert all(int(a["hi"]) + 1 == int(b["lo"]) for a, b in zip(ordered, ordered[1:]))
    for record in ordered:
        lo, hi, midpoint = (int(record[k]) for k in ("lo", "hi", "midpoint"))
        re_moments = [0] * len(record["moments"])
        im_moments = [0] * len(record.get("imag_moments", [0] * len(re_moments)))
        mass = nonzero = 0
        for n in range(lo, hi + 1):
            re, im = coefficients[n - 1]
            if re or im:
                nonzero += 1
                mass += abs(re) + abs(im)
            delta = n - midpoint
            power = 1
            for j in range(len(re_moments)):
                re_moments[j] += re * power
                im_moments[j] += im * power
                power *= delta
        assert mass == int(record["mass"]), f"bin mass mismatch [{lo},{hi}]"
        assert nonzero == int(record["nonzero_count"]), f"bin count mismatch [{lo},{hi}]"
        assert re_moments == list(map(int, record["moments"])), f"real moments mismatch [{lo},{hi}]"
        expected_im = list(map(int, record.get("imag_moments", [0] * len(im_moments))))
        assert im_moments == expected_im, f"imaginary moments mismatch [{lo},{hi}]"


def eval_poly(polynomial, x):
    value = polynomial[-1]
    for coefficient in reversed(polynomial[:-1]):
        value = value * x + coefficient
    return value


def pointwise_kernel_sum(coefficients, kernels, conductor: int):
    """Sum quadratic Taylor centers term-by-term and debit each piece remainder."""
    from flint import acb, arb

    t = kernels.scale(conductor)
    primary = acb(0)
    dual = acb(0)
    raw_error = arb(0)
    for n, (re, im) in enumerate(coefficients, start=1):
        if not (re or im):
            continue
        x = t * n
        for center, left, poly_a, poly_b, remainder in kernels.pieces:
            if left < x <= center:
                delta = x - center
                primary += acb(re, im) * eval_poly(poly_a, delta)
                dual += acb(re, -im) * eval_poly(poly_b, delta)
                raw_error += (abs(re) + abs(im)) * remainder
                break
        else:
            raise AssertionError(f"kernel grid does not cover x=t*{n}")
    prefactor = kernels.prefactor(conductor)
    return primary * prefactor, dual * prefactor, raw_error * prefactor


def main() -> None:
    if not __debug__:
        raise RuntimeError("Python assertions are required")
    for label, (path, expected) in PINS.items():
        actual = sha(path)
        if actual != expected:
            raise AssertionError(f"{label} hash mismatch: {actual}")

    from flint import acb, arb, ctx
    import flint

    ctx.prec = 384
    arithmetic = json.loads(ARITH.read_text())
    moments_data = json.loads(MOMENTS.read_text())
    frozen = json.loads(EVALUATION.read_text())
    sector = next(s for s in arithmetic["sectors"] if s["mask"] == 1586)
    source_row = next(r for r in sector["rows"] if r["twist"] == 1)
    moment_row = next(r for r in moments_data["rows"] if r["twist"] == 1)
    frozen_row = next(r for s in frozen["sectors"] if s["mask"] == 1586
                      for r in s["rows"] if r["twist"] == 1)
    assert sector["dimension"] == 2
    assert source_row["gamma"] == [0, 1] and source_row["root_number"] == 1
    assert source_row["conductor"] == moment_row["conductor"] == frozen_row["conductor"] == 240240
    assert moment_row["N"] == frozen_row["N"] == 3922
    assert frozen_row["kind"] == "quadratic"
    assert frozen_row["status"] == "PASS signed real AFE, exact root number+1"
    assert frozen_row["rankin_beta"] == "6/5"
    for key in ("twist", "conductor", "gamma", "root_number", "factor_multiplicity",
                "bad_euler_denominators"):
        if source_row[key] != moment_row[key]:
            raise AssertionError(f"arithmetic/moment source mismatch at {key}")

    coeff = load_module("independent_rank2_coefficients", COEFF_SOURCE)
    coefficients = coeff.rank2_first(source_row, sector, int(moment_row["N"]))
    if len(coefficients) != int(moment_row["N"]):
        raise AssertionError("coefficient reconstruction length mismatch")
    signed_vector = [tuple(v) for v in [[0, 0], *coefficients]]
    vector_hash = hashlib.sha256(json.dumps(signed_vector).encode()).hexdigest()
    if vector_hash != moment_row["signed_coefficients_sha256"]:
        raise AssertionError(f"complete signed coefficient hash mismatch: {vector_hash}")
    if any(im for _re, im in coefficients):
        raise AssertionError("selected quadratic row unexpectedly has nonreal coefficients")
    nonzero = sum(bool(re or im) for re, im in coefficients)
    expected_nonzero = sum(int(b["nonzero_count"]) for b in moment_row["bins"])
    if nonzero != expected_nonzero or nonzero != 562:
        raise AssertionError(f"full nonzero count mismatch: {nonzero} vs {expected_nonzero}")
    check_exact_bins(coefficients, moment_row["bins"], int(moment_row["N"]))

    afe = load_module("pinned_quadratic_split_kernel", AFE_SOURCE)
    sigma_q = Fraction(6001, 6000)
    kernels = afe.SplitKernels(afe.rational(sigma_q), kind="quadratic")
    A, B, interpolation = pointwise_kernel_sum(
        coefficients, kernels, int(source_row["conductor"]))
    if not A.imag.contains(0) or not B.imag.contains(0):
        raise AssertionError("real signed AFE row produced a finite sum excluding the real axis")
    if not contained_complex_in_center_plus_error(A, frozen_row["A_finite"],
                                                   frozen_row["one_side_interpolation_error"]):
        raise AssertionError("pointwise primary sum escapes frozen center plus interpolation debit")
    if not contained_complex_in_center_plus_error(B, frozen_row["B_finite"],
                                                   frozen_row["one_side_interpolation_error"]):
        raise AssertionError("pointwise dual sum escapes frozen center plus interpolation debit")
    _int_lo, int_hi = source_interval(frozen_row["one_side_interpolation_error"])
    if endpoint_fraction(interpolation.upper()) > int_hi:
        raise AssertionError("direct interpolation remainder exceeds frozen allowance")

    # Conditional global tail: the primitive finite-image degree-two factor
    # has |a_n| <= d_2(n), so its absolute Rankin mass is bounded by zeta(beta)^2.
    beta = afe.rational(Fraction(frozen_row["rankin_beta"]))
    n0 = int(moment_row["N"]) + 1
    t = kernels.scale(int(source_row["conductor"]))
    x = t * n0
    assert x > beta - 1
    tail = (kernels.prefactor(int(source_row["conductor"])) * beta.zeta()**2
            * arb(n0)**beta * afe.quadratic_majorant(x))
    if not overlap(tail, frozen_row["one_side_truncation_error"]):
        raise AssertionError("direct Rankin tail does not overlap frozen tail interval")
    error = interpolation + tail
    signed_center = A + B
    if signed_center.real.lower() - 2 * error.upper() <= 0:
        raise AssertionError("signed real AFE lower bound is not positive")
    modulus_upper = abs(signed_center).upper() + 2 * error.upper()

    s = afe.rational(sigma_q)
    bad_multiplier = arb(1)
    for ptext, polynomial in source_row["bad_euler_denominators"].items():
        p = int(ptext)
        z = arb(p)**(-s)
        factor = acb(0)
        for j, (re, im) in enumerate(polynomial):
            factor += acb(int(re), int(im)) * z**j
        if not abs(factor) > 0:
            raise AssertionError(f"bad Euler denominator vanishes at p={p}")
        bad_multiplier *= abs(factor)
    if not overlap(bad_multiplier, frozen_row["bad_multiplier_modulus"]):
        raise AssertionError("direct bad-factor product does not overlap frozen interval")
    removed_upper = (modulus_upper * bad_multiplier).upper()
    log_upper = removed_upper.log().upper()
    printed_log_interval = source_interval(frozen_row["log_abs_L_S_upper"])
    printed_log_upper = printed_log_interval[1]
    direct_log_upper = endpoint_fraction(log_upper)
    comparison_margin = printed_log_upper - direct_log_upper
    passed = comparison_margin >= 0

    result = {
        "status": ("PASS direct pointwise H6 mixed-quadratic AFE row replay"
                   if passed else "FAIL direct upper exceeds frozen allowance"),
        "scope": "one conditional H6 mixed-quadratic factor row; not a proof of global H",
        "sector_mask": 1586, "twist": 1, "degree": 2,
        "conductor": int(source_row["conductor"]), "gamma": source_row["gamma"],
        "root_number": source_row["root_number"], "sigma": str(sigma_q),
        "N": int(moment_row["N"]), "coefficients_reconstructed": len(coefficients),
        "signed_coefficient_vector_sha256": vector_hash,
        "nonzero_coefficients": nonzero, "exact_moment_bins_checked": len(moment_row["bins"]),
        "precision_bits": ctx.prec, "python_flint_version": flint.__version__,
        "flint_version": flint.__FLINT_VERSION__, "kernel_piece_count": len(kernels.pieces),
        "A_pointwise": {"real": encode_arb(A.real), "imag": encode_arb(A.imag)},
        "B_pointwise": {"real": encode_arb(B.real), "imag": encode_arb(B.imag)},
        "A_within_frozen_center_plus_interpolation": True,
        "B_within_frozen_center_plus_interpolation": True,
        "pointwise_interpolation_debit": encode_arb(interpolation),
        "frozen_interpolation_debit": frozen_row["one_side_interpolation_error"],
        "one_side_tail": encode_arb(tail), "rankin_beta": frozen_row["rankin_beta"],
        "signed_finite_sum": {"real": encode_arb(signed_center.real),
                              "imag": encode_arb(signed_center.imag)},
        "bad_multiplier": encode_arb(bad_multiplier),
        "modulus_upper": encode_arb(modulus_upper),
        "removed_modulus_upper": encode_arb(removed_upper),
        "log_L_S_upper": encode_arb(log_upper),
        "printed_log_L_S_upper": frozen_row["log_abs_L_S_upper"],
        "comparison_diagnostic": {
            "direct_log_upper_exact_fraction": f"{direct_log_upper.numerator}/{direct_log_upper.denominator}",
            "printed_log_upper_exact_fraction": f"{printed_log_upper.numerator}/{printed_log_upper.denominator}",
            "printed_minus_direct_margin_exact_fraction": f"{comparison_margin.numerator}/{comparison_margin.denominator}",
            "printed_minus_direct_margin_decimal": str(float(comparison_margin)),
            "source_modulus_upper": frozen_row["modulus_upper"],
            "source_removed_modulus_upper": frozen_row["removed_modulus_upper"],
            "signed_center": {"real": encode_arb(signed_center.real),
                              "imag": encode_arb(signed_center.imag)},
            "combined_two_side_error": encode_arb(2 * error),
        },
        "row_allowance_comparison_passed": passed,
        "coefficient_method": "exact quadratic residue/Euler recurrence; complete signed-vector hash matched and every stored exact moment bin checked",
        "kernel_method": "pointwise coefficient summation using existing pinned nonpositive-afe.py quadratic SplitKernels and explicit Taylor remainder; same python-flint/Arb backend, not a new kernel backend",
        "conditional_assumptions": [
            "the pinned conductor, gamma=[0,1], and root number +1 describe the intended primitive entire degree-two L-function with its conjugation-compatible functional equation",
            "the finite-image all-prime coefficient bound |a_n| <= d_2(n) holds globally, yielding zeta(beta)^2 Rankin majorant",
            "the listed bad-prime Euler denominator polynomials are the complete local factors removed in L_S",
            "the pinned quadratic Mellin-kernel majorant and Rankin tail inequality apply to this row",
            "python-flint/Arb outward interval arithmetic and the pinned SplitKernels Taylor remainder derivation are sound",
        ],
        "source_sha256": {label: expected for label, (_path, expected) in PINS.items()},
        "scope_limitations": [
            "the exact coefficient vector hash and finite moment checks do not prove the all-n coefficient bound",
            "this row does not prove the representation-to-factor identity or global hypothesis H",
            "the replay shares the pinned SplitKernels kernel and Arb/FLINT backend with the frozen evaluator",
        ],
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if not passed:
        raise AssertionError("direct row upper exceeds frozen allowance; diagnostics were saved")


if __name__ == "__main__":
    main()
