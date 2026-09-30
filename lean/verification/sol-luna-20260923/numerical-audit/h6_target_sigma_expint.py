#!/usr/bin/env python3
"""Independent Arb exponential-integral replay of H6 mask 1586, twist +1.

This route derives the quadratic AFE weights directly from the mixed gamma
factor and Arb's generalized exponential integral; it does not import or call
the manuscript SplitKernels evaluator. The calculation is staged only; run it
through the shared guarded slot after allocation.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import math
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PUB = REPO / "publication"
RESEARCH = PUB / "nonabelian-dyadic-lower-bound/research"
ARITH = RESEARCH / "h6-low-degree-arithmetic.json"
MOMENTS = RESEARCH / "h6-low-degree-moments-1586.json"
TARGET = RESEARCH / "h7-inherited-euler-12000.json"
ANALYTIC = REPO / "lean-formalization/verification/external-zeta-20260922/analytic-replay-20260922.json"
COEFF_SOURCE = REPO / "lean-formalization/verification/sol-luna-20260922/numerics_hecke_coeff_check.py"
OLD_DIRECT = HERE / "h6_target_sigma_direct.json"
OLD_AGGREGATE = HERE / "h6_target_aggregate_replacement.json"
OUTPUT = HERE / "h6_target_sigma_expint.json"
TARGET_SIGMA = Fraction(12001, 12000)

PINS = {
    "h6-low-degree-arithmetic.json": (ARITH, "b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771"),
    "h6-low-degree-moments-1586.json": (MOMENTS, "a7e65537a05389f11115a8cf64c186ead6b1dc4973a8c5f862f31a34fdeb40f1"),
    "h7-inherited-euler-12000.json": (TARGET, "b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f"),
    "h7-inherited-analytic-replay.json": (ANALYTIC, "34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e"),
    "numerics_hecke_coeff_check.py": (COEFF_SOURCE, "3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329"),
    "h6_target_sigma_direct.json": (OLD_DIRECT, "d35c52ea39918684b39c456c1e1fd6f3cdad3b61e177f0eeea06c5457e7eff58"),
    "h6_target_aggregate_replacement.json": (OLD_AGGREGATE, "35ec8d17c01f716663e9e7c7b64862413efd65cbae6807851b3d06536e360f27"),
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
    m, e = int(record["mantissa"]), int(record["exponent"])
    return Fraction(m * (2 ** e)) if e >= 0 else Fraction(m, 2 ** (-e))


def source_interval(record: dict) -> tuple[Fraction, Fraction]:
    return source_endpoint(record["lower"]), source_endpoint(record["upper"])


def encode_arb(value) -> dict:
    def one(endpoint):
        m, e = endpoint.man_exp()
        return {"mantissa": str(m), "exponent": int(e)}
    return {"lower": one(value.lower()), "upper": one(value.upper()),
            "display": value.str(38, radius=True)}


def contained_in_center_plus_error(value, center: dict, error: dict) -> bool:
    lo, hi = source_interval(center)
    _err_lo, err_hi = source_interval(error)
    return lo - err_hi <= endpoint_fraction(value.lower()) and endpoint_fraction(value.upper()) <= hi + err_hi


def overlap(value, source: dict) -> bool:
    lo, hi = source_interval(source)
    return endpoint_fraction(value.lower()) <= hi and lo <= endpoint_fraction(value.upper())


def exact_bins(coefficients: list[tuple[int, int]], bins: list[dict], nmax: int) -> None:
    ordered = sorted(bins, key=lambda row: int(row["lo"]))
    if not ordered or int(ordered[0]["lo"]) != 1 or int(ordered[-1]["hi"]) != nmax:
        raise AssertionError("moment bins do not cover [1,N]")
    for left, right in zip(ordered, ordered[1:]):
        if int(left["hi"]) + 1 != int(right["lo"]):
            raise AssertionError("moment-bin gap/overlap")
    for row in ordered:
        lo, hi, mid = (int(row[k]) for k in ("lo", "hi", "midpoint"))
        re_m = [0] * len(row["moments"])
        im_m = [0] * len(row.get("imag_moments", [0] * len(re_m)))
        mass = count = 0
        for n in range(lo, hi + 1):
            re, im = coefficients[n - 1]
            if re or im:
                count += 1
                mass += abs(re) + abs(im)
            power = 1
            for j in range(len(re_m)):
                re_m[j] += re * power
                im_m[j] += im * power
                power *= n - mid
        if mass != int(row["mass"]) or count != int(row["nonzero_count"]):
            raise AssertionError(f"mass/count mismatch in [{lo},{hi}]")
        if re_m != list(map(int, row["moments"])):
            raise AssertionError(f"real moment mismatch in [{lo},{hi}]")
        if im_m != list(map(int, row.get("imag_moments", [0] * len(im_m)))):
            raise AssertionError(f"imaginary moment mismatch in [{lo},{hi}]")


def direct_expint_sums(coefficients: list[tuple[int, int]], t, s):
    """Evaluate A,B using E_v(x)=integral_1^infinity exp(-xu)u^(-v)du.

    E_(1-s)(tn) is the primary incomplete-gamma weight and E_s(tn) the
    dual weight. For real coefficients the conjugate coefficient sequence
    is the same, and the stipulated root number +1 gives A+B.
    """
    from flint import arb
    a, b = arb(0), arb(0)
    for n, (re, im) in enumerate(coefficients, start=1):
        if im:
            raise AssertionError("selected row is not real coefficientwise")
        if re:
            x = t * n
            a += re * x.expint(1 - s)
            b += re * x.expint(s)
    prefactor = t ** s / s.gamma()
    return prefactor * a, prefactor * b


def elementary_tails(s, q: int, nmax: int):
    """Rigorous conditional tails using |a_n|<=d2(n)<=2 sqrt(n).

    Put delta=s-1, m=N+1, x0=t*m. For x>=x0>delta,
      E_(1-s)(x)=int_1^inf u^delta e^(-xu)du <= e^-x/(x-delta),
      E_s(x)=int_1^inf u^-s e^(-xu)du <= e^-x/x.
    Also sum_{n>=m} e^(-tn)=e^(-tm)/(1-e^-t), sqrt(n)>=sqrt(m),
    and (tn-delta)^-1 <= (tn)^-1/(1-delta/x0).
    These yield the two bounds below. All operations are outward Arb.
    """
    from flint import arb
    t = 2 * arb.pi() / arb(q).sqrt()
    delta = s - 1
    m = nmax + 1
    x0 = t * m
    if not (t > 0 and x0 > delta):
        raise AssertionError("tail inequalities require t>0 and t(N+1)>sigma-1")
    prefactor = t ** s / s.gamma()
    geom = 1 / (1 - (-t).exp())
    e0 = (-x0).exp()
    common = prefactor * 2 * e0 * geom / (t * arb(m).sqrt())
    primary = common / (1 - delta / x0)
    dual = common
    return t, primary, dual


def main() -> None:
    if not __debug__:
        raise RuntimeError("Python assertions are required")
    started = time.monotonic()
    for label, (path, digest) in PINS.items():
        actual = sha(path)
        if actual != digest:
            raise AssertionError(f"{label} SHA mismatch: {actual}")

    from flint import acb, arb, ctx
    import flint
    ctx.prec = 384

    arithmetic = json.loads(ARITH.read_text())
    moments = json.loads(MOMENTS.read_text())
    target = json.loads(TARGET.read_text())
    analytic = json.loads(ANALYTIC.read_text())
    old_direct = json.loads(OLD_DIRECT.read_text())
    old_aggregate = json.loads(OLD_AGGREGATE.read_text())

    target_rel = str(TARGET.relative_to(PUB))
    table_hash = analytic["printed_analytic_table_check"]["source_sha256"].get(target_rel)
    replay_hash = analytic["analytic_replay"]["replay_input_sha256"].get(target_rel)
    binding = (table_hash == sha(TARGET) and replay_hash == sha(TARGET)
               and analytic.get("all_analytic_factors_reevaluated") is True)
    if not binding:
        raise AssertionError("target receipt not hash-bound in consolidated analytic replay")

    sector = next(x for x in arithmetic["sectors"] if x["mask"] == 1586)
    row = next(x for x in sector["rows"] if x["twist"] == 1)
    mrow = next(x for x in moments["rows"] if x["twist"] == 1)
    tsector = next(x for x in target["sectors"] if x.get("stage") == "H6-low" and x["mask"] == 1586)
    trow = next(x for x in tsector["rows"] if x["twist"] == 1)
    if (sector["dimension"] != 2 or row["gamma"] != [0, 1] or row["root_number"] != 1
        or target.get("sigma") != str(TARGET_SIGMA) or trow.get("kind") != "quadratic"
        or trow.get("status") != "PASS signed real AFE, exact root number+1"
        or row["conductor"] != 240240 or mrow["N"] != 3922
        or trow["conductor"] != row["conductor"] or trow["N"] != mrow["N"]
        or trow.get("rankin_beta") != "6/5" or trow.get("multiplicity") != 1):
        raise AssertionError("target row identity/normalization mismatch")
    for key in ("twist", "conductor", "gamma", "root_number", "factor_multiplicity", "bad_euler_denominators"):
        if row[key] != mrow[key]:
            raise AssertionError(f"arithmetic/moment mismatch in {key}")
    if old_direct.get("status") != "FAIL target-sigma direct upper exceeds target row allowance":
        raise AssertionError("prior strict SplitKernels FAIL changed or missing")
    if not old_aggregate.get("status", "").startswith("PASS exact target mixed-quadratic aggregate replacement"):
        raise AssertionError("prior target aggregate PASS changed or missing")

    coeff_module = load_module("h6_rank2_coefficients_expint", COEFF_SOURCE)
    coefficients = [tuple(map(int, x)) for x in coeff_module.rank2_first(row, sector, int(mrow["N"]))]
    if len(coefficients) != int(mrow["N"]):
        raise AssertionError("coefficient vector length mismatch")
    vector = [(0, 0), *coefficients]
    coeff_hash = hashlib.sha256(json.dumps(vector).encode()).hexdigest()
    if coeff_hash != mrow["signed_coefficients_sha256"]:
        raise AssertionError("complete signed coefficient vector SHA mismatch")
    exact_bins(coefficients, mrow["bins"], int(mrow["N"]))

    s = arb(TARGET_SIGMA.numerator) / TARGET_SIGMA.denominator
    q, nmax = int(row["conductor"]), int(mrow["N"])
    t, primary_tail, dual_tail = elementary_tails(s, q, nmax)
    A, B = direct_expint_sums(coefficients, t, s)
    finite_checks = {
        "A_within_target_center_plus_interpolation": contained_in_center_plus_error(
            A, trow["A_finite"]["real"], trow["one_side_interpolation_error"]),
        "B_within_target_center_plus_interpolation": contained_in_center_plus_error(
            B, trow["B_finite"]["real"], trow["one_side_interpolation_error"]),
    }
    signed = A + B
    error = primary_tail + dual_tail
    positive = signed.lower() - error.upper() > 0
    modulus_upper = abs(signed).upper() + error.upper()

    bad = arb(1)
    for ptext, polynomial in row["bad_euler_denominators"].items():
        p = int(ptext)
        z = arb(p) ** (-s)
        value = acb(0)
        for j, (re, im) in enumerate(polynomial):
            value += acb(int(re), int(im)) * z ** j
        if not abs(value) > 0:
            raise AssertionError(f"bad Euler factor vanishes at p={p}")
        bad *= abs(value)
    bad_match = overlap(bad, trow["bad_multiplier_modulus"])
    removed = (modulus_upper * bad).upper()
    log_upper = removed.log().upper()
    target_hi = source_interval(trow["log_abs_L_S_upper"])[1]
    direct_endpoint = endpoint_fraction(log_upper)
    margin = target_hi - direct_endpoint
    passed = all(finite_checks.values()) and positive and bad_match and margin >= 0

    result = {
        "status": ("PASS target-sigma independent expint H6 AFE row" if passed else
                   "FAIL target-sigma expint endpoint/consistency check"),
        "scope": "one conditional H6 mask-1586 twist+1 quadratic AFE row at sigma 12001/12000",
        "mask": 1586, "twist": 1, "degree": 2, "multiplicity": int(trow["multiplicity"]),
        "conductor": q, "gamma": row["gamma"], "root_number": row["root_number"],
        "sigma": str(TARGET_SIGMA), "N": nmax, "coefficients_reconstructed": len(coefficients),
        "nonzero_coefficients": sum(bool(a or b) for a, b in coefficients),
        "coefficient_vector_sha256": coeff_hash, "moment_bins_checked": len(mrow["bins"]),
        "precision_bits": ctx.prec, "python_flint_version": flint.__version__,
        "flint_version": flint.__FLINT_VERSION__,
        "gamma_normalization": "Gamma_R(s)Gamma_R(s+1)=2(2pi)^(-s)Gamma(s); t=2pi/sqrt(Q); prefactor=t^s/Gamma(s)",
        "kernel_derivation": "Arb E_v(x)=integral_1^infinity exp(-xu)u^(-v)du; A uses E_(1-s)(tn), B uses E_s(tn); epsilon=+1 and real coefficients give A+B",
        "A_expint": encode_arb(A), "B_expint": encode_arb(B),
        "A_finite_consistency": finite_checks["A_within_target_center_plus_interpolation"],
        "B_finite_consistency": finite_checks["B_within_target_center_plus_interpolation"],
        "primary_tail_upper": encode_arb(primary_tail), "dual_tail_upper": encode_arb(dual_tail),
        "combined_tail_upper": encode_arb(error), "tail_formula": "d2(n)<=2sqrt(n), E_(1-s)(x)<=e^-x/(x-(s-1)), E_s(x)<=e^-x/x; geometric sum from n=N+1",
        "signed_A_plus_B": encode_arb(signed), "signed_positive_after_tail": positive,
        "bad_multiplier": encode_arb(bad), "bad_multiplier_overlaps_target": bad_match,
        "removed_modulus_upper": encode_arb(removed), "log_L_S_upper": encode_arb(log_upper),
        "target_log_L_S_upper": trow["log_abs_L_S_upper"],
        "comparison": {
            "direct_upper_exact": f"{direct_endpoint.numerator}/{direct_endpoint.denominator}",
            "target_upper_exact": f"{target_hi.numerator}/{target_hi.denominator}",
            "target_minus_direct_exact": f"{margin.numerator}/{margin.denominator}",
            "target_minus_direct_decimal": str(float(margin)),
            "pass": margin >= 0,
        },
        "prior_split_kernel_row_status": old_direct["status"],
        "prior_split_kernel_row_receipt_sha256": sha(OLD_DIRECT),
        "prior_target_aggregate_status": old_aggregate["status"],
        "prior_target_aggregate_receipt_sha256": sha(OLD_AGGREGATE),
        "target_receipt_binding": {
            "target_sha256": sha(TARGET), "consolidated_table_source_sha256": table_hash,
            "analytic_replay_input_sha256": replay_hash,
            "all_analytic_factors_reevaluated": analytic["all_analytic_factors_reevaluated"],
            "verified": binding,
        },
        "source_sha256": {name: digest for name, (_path, digest) in PINS.items()},
        "checker_sha256": sha(Path(__file__)), "seconds": time.monotonic() - started,
        "conditional_assumptions": [
            "the row is the intended primitive entire degree-two factor with conductor 240240 and gamma_R(s)Gamma_R(s+1)",
            "its conjugation-compatible functional equation has root number +1, giving the signed real A+B formula",
            "the completed L-function is connected to its coefficients by L(w)=sum_n a_n n^(-w) in a right half-plane",
            "sufficient vertical growth/contour decay justifies the Mellin-contour shift used to derive the two expint weights; entireness and the functional equation alone are not stated as sufficient",
            "the listed bad Euler denominators are the complete removed local factors",
            "the global coefficient bound |a_n|<=d_2(n) holds, including the infinite tail",
            "Arb/python-flint generalized expint, gamma, exponential, logarithm, and ball arithmetic give valid outward enclosures",
        ],
        "limitations": [
            "finite coefficient/hash/bin checks do not prove the global coefficient bound or row identity",
            "this direct kernel is independent of SplitKernels but uses the same Arb/FLINT interval backend",
            "this single row and its aggregate substitution do not prove H",
        ],
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if not passed:
        raise AssertionError("expint row endpoint/consistency failed; diagnostics were saved")


if __name__ == "__main__":
    main()
