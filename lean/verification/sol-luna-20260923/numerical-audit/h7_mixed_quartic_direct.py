#!/usr/bin/env python3
"""Hash-pinned direct coefficient-sum replay for H7 mask 274, twist +1.

This is source-complete but intentionally not yet run. Coordinate any numerical
execution with the parent and use the shared guarded-build lock. The script
reconstructs coefficients, checks all exact moment bins, sums each coefficient
against the pinned mixed-quartic SplitKernels Taylor piece, debits its explicit
kernel remainder and Rankin tail, and compares with the frozen row allowance.
It reuses the existing SplitKernels / python-flint backend; it is not a new
analytic-kernel backend.
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
ARITH = RESEARCH / "h7-low-arithmetic.json"
MOMENTS = RESEARCH / "h7-low-moments-274.json"
EVALUATION = RESEARCH / "h7-low-euler-12000.json"
LOW_EULER_SOURCE = RESEARCH / "h7-low-euler.py"
LOW_ARITH_SOURCE = RESEARCH / "h7-low-arithmetic.py"
LOW_EVALUATOR_SOURCE = RESEARCH / "h6-low-degree-euler.py"
HEECKE_AFE = PUB / "unit-distance-lower-bound/certificates/hecke_afe.py"
EXACT_GROUP = PUB / "unit-distance-lower-bound/certificates/exact_group.py"
DEFAULT_OUTPUT = HERE / "h7_mixed_quartic_direct.json"

PINS = {
    "h7-low-arithmetic.json": (ARITH, "4453a7fe7549ec3e189817e9081bb24c1d3244c3b1249604ab811ab289bf554f"),
    "h7-low-moments-274.json": (MOMENTS, "0777fc81c8a9a6bcff795371e3f7f42095d86e268f141c0dba72777b40e82227"),
    "h7-low-euler-12000.json": (EVALUATION, "e18811d9a91281e1fc3fcc81d49130ad5968ba5611e6e649d7061addea32525e"),
    "h7-low-euler.py": (LOW_EULER_SOURCE, "012675f3e251a857c8e9c74046513f84d261a08dcd7c26535cac0737ac5c6cbd"),
    "h7-low-arithmetic.py": (LOW_ARITH_SOURCE, "7105e8b7816837c059ae6b4f4f31be3750c0eb89af5363ab9a8624bc0685540b"),
    "h6-low-degree-euler.py": (LOW_EVALUATOR_SOURCE, "9fdee8fe5bd9fcbc90c9b28ccbdd0ec5066d49b8b52757ee3f20cc89af707f38"),
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
        if mass != int(record["mass"]):
            raise AssertionError(f"exact moment bin mass mismatch at [{lo},{hi}]")
        if nonzero != int(record["nonzero_count"]):
            raise AssertionError(f"exact moment bin count mismatch at [{lo},{hi}]")
        if re_moments != list(map(int, record["moments"])):
            raise AssertionError(f"exact real moments mismatch at [{lo},{hi}]")
        expected_im = list(map(int, record.get("imag_moments", [0] * len(im_moments))))
        if im_moments != expected_im:
            raise AssertionError(f"exact imaginary moments mismatch at [{lo},{hi}]")


def eval_poly(polynomial, x):
    value = polynomial[-1]
    for coefficient in reversed(polynomial[:-1]):
        value = value * x + coefficient
    return value


def pointwise_kernel_sum(coefficients, kernels, conductor: int):
    """Sum Taylor centers term-by-term; return A, B and one-side kernel error."""
    from flint import acb, arb

    t = kernels.scale(conductor)
    primary = acb(0)
    dual = acb(0)
    raw_error = arb(0)
    pieces = kernels.pieces
    for n, (re, im) in enumerate(coefficients, start=1):
        if not (re or im):
            continue
        x = t * n
        match = None
        for center, left, poly_a, poly_b, remainder in pieces:
            if left < x <= center:
                match = (center, poly_a, poly_b, remainder)
                break
        if match is None:
            raise AssertionError(f"kernel grid does not cover x=t*{n}")
        center, poly_a, poly_b, remainder = match
        delta = x - center
        ka = eval_poly(poly_a, delta)
        kb = eval_poly(poly_b, delta)
        primary += acb(re, im) * ka
        dual += acb(re, -im) * kb
        raw_error += (abs(re) + abs(im)) * remainder
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
    sector = next(s for s in arithmetic["sectors"] if s["mask"] == 274)
    source_row = next(r for r in sector["rows"] if r["twist"] == 1)
    moment_row = next(r for r in moments_data["rows"] if r["twist"] == 1)
    frozen_row = next(r for s in frozen["sectors"] if s["mask"] == 274
                      for r in s["rows"] if r["twist"] == 1)
    assert sector["dimension"] == 4
    assert source_row["gamma"] == [0, 0, 1, 1] and source_row["root_number"] == 1
    for key in ("twist", "conductor", "gamma", "root_number", "quartic_exponent",
                "bad_euler_denominators", "first128_complex_coefficients"):
        if source_row[key] != moment_row[key]:
            raise AssertionError(f"arithmetic/moment input mismatch at {key}")
    assert source_row["twist"] == 1
    assert moment_row["N"] == frozen_row["N"] == 192193
    assert source_row["conductor"] == frozen_row["conductor"] == 577152576
    assert frozen_row["status"] == "PASS signed real AFE, exact root number+1"
    assert frozen_row["moment_coefficient_weight_power"] == 0
    assert frozen_row["rankin_beta"] == "5/4"

    coeff = load_module("mixed_quartic_coefficient_rules", COEFF_SOURCE)
    coefficients = coeff.higher_rank_prefix(source_row, sector, int(moment_row["N"]))
    if len(coefficients) != int(moment_row["N"]):
        raise AssertionError("full coefficient reconstruction has wrong length")
    if coefficients[:128] != source_row["first128_complex_coefficients"]:
        raise AssertionError("reconstructed coefficient prefix differs from arithmetic row")
    if coefficients[:128] != moment_row["first128_complex_coefficients"]:
        raise AssertionError("reconstructed coefficient prefix differs from moment row")
    if any(im for _re, im in coefficients):
        raise AssertionError("selected real mixed-quartic row has nonreal coefficients")
    nonzero = sum(bool(re or im) for re, im in coefficients)
    expected_nonzero = sum(int(b["nonzero_count"]) for b in moment_row["bins"])
    if nonzero != expected_nonzero or nonzero != 2255:
        raise AssertionError(f"full nonzero count {nonzero} differs from pinned total {expected_nonzero}")
    check_exact_bins(coefficients, moment_row["bins"], int(moment_row["N"]))

    afe = load_module("pinned_mixed_quartic_split_kernel", AFE_SOURCE)
    sigma_q = Fraction(12001, 12000)
    kernels = afe.SplitKernels(afe.rational(sigma_q), kind="quartic")
    A, B, interpolation = pointwise_kernel_sum(
        coefficients, kernels, int(source_row["conductor"]))
    if not A.imag.contains(0) or not B.imag.contains(0):
        raise AssertionError("real signed AFE row produced a finite sum excluding the real axis")
    if not contained_complex_in_center_plus_error(A, frozen_row["A_finite"],
                                                   frozen_row["one_side_interpolation_error"]):
        raise AssertionError("direct pointwise primary sum escapes frozen center plus interpolation error")
    if not contained_complex_in_center_plus_error(B, frozen_row["B_finite"],
                                                   frozen_row["one_side_interpolation_error"]):
        raise AssertionError("direct pointwise dual sum escapes frozen center plus interpolation error")
    _interpolation_lo, interpolation_hi = source_interval(frozen_row["one_side_interpolation_error"])
    if endpoint_fraction(interpolation.upper()) > interpolation_hi:
        raise AssertionError("pointwise Taylor remainder exceeds frozen interpolation allowance")

    # For the omitted coefficients, the pinned quartic split-kernel majorant
    # and the global finite-image bound |a_n| <= d_4(n) give zeta(beta)^4.
    # This all-n estimate is an analytic assumption, not a consequence of the
    # finite coefficient reconstruction above.
    beta = afe.rational(Fraction(frozen_row["rankin_beta"]))
    n0 = int(moment_row["N"]) + 1
    t = kernels.scale(int(source_row["conductor"]))
    x = 2 * (t * n0).sqrt()
    assert x > 2 * beta - arb(3) / 2
    tail = kernels.prefactor(int(source_row["conductor"])) * beta.zeta()**4 * arb(n0)**beta * afe.majorant(x)
    if not overlap(tail, frozen_row["one_side_truncation_error"]):
        raise AssertionError("direct Rankin-tail interval does not overlap frozen tail interval")
    error = interpolation + tail
    signed_center = A + B
    if signed_center.real.lower() - 2 * error.upper() <= 0:
        raise AssertionError("signed real AFE lower bound is not positive")
    modulus_upper = abs(signed_center).upper() + 2 * error.upper()

    # Remove exactly the seven listed bad Euler factors. This product's global
    # completeness is part of the stated analytic row assumptions.
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
    printed_log_upper = source_interval(frozen_row["log_abs_L_S_upper"])[1]
    passed = endpoint_fraction(log_upper) <= printed_log_upper
    if not passed:
        raise AssertionError("direct row upper bound exceeds frozen log allowance")

    result = {
        "status": "PASS direct pointwise mixed-quartic AFE row replay" if passed else "FAIL",
        "scope": "one conditional H7 mixed-quartic factor row; not a proof of global H",
        "sector_mask": 274, "twist": 1, "degree": 4, "conductor": int(source_row["conductor"]),
        "gamma": source_row["gamma"], "root_number": source_row["root_number"],
        "sigma": str(sigma_q), "N": n0 - 1, "coefficients_reconstructed": len(coefficients),
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
        "signed_finite_sum": {"real": encode_arb(signed_center.real), "imag": encode_arb(signed_center.imag)},
        "bad_multiplier": encode_arb(bad_multiplier), "modulus_upper": encode_arb(modulus_upper),
        "removed_modulus_upper": encode_arb(removed_upper), "log_L_S_upper": encode_arb(log_upper),
        "printed_log_L_S_upper": frozen_row["log_abs_L_S_upper"],
        "row_allowance_comparison_passed": passed,
        "coefficient_method": "pinned independent exact genus/local-Euler recurrence through N; first128 and every exact moment bin checked",
        "kernel_method": "pointwise coefficient summation using existing pinned nonpositive-afe.py SplitKernels quartic Taylor pieces and their explicit remainder; same python-flint/Arb backend, not a new kernel backend",
        "conditional_assumptions": [
            "the pinned conductor, gamma=[0,0,1,1], and root number +1 identify the intended primitive entire degree-four L-function with its stipulated conjugation-compatible functional equation",
            "the local Euler recurrence identifies the selected row and the finite-image all-prime coefficient bound |a_n| <= d_4(n) holds for every n",
            "the listed bad-prime denominator polynomials are the complete local factors removed in L_S",
            "the pinned quartic Mellin-kernel majorant and Rankin tail inequality apply to this row",
            "python-flint/Arb outward interval arithmetic and the pinned SplitKernels Taylor remainder derivation are sound",
        ],
        "source_sha256": {label: expected for label, (_path, expected) in PINS.items()},
        "scope_limitations": [
            "finite coefficient checks through N do not prove the all-n coefficient bound",
            "this row replay does not prove the representation-to-factor identity or global hypothesis H",
            "the direct summation shares the pinned SplitKernels analytic kernel and Arb/FLINT interval backend with the frozen evaluator",
        ],
    }
    DEFAULT_OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
