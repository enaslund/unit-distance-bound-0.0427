#!/usr/bin/env python3
"""Independent expint-kernel replay for all H6 mask-1586 quadratic rows.

Source-ready batch checker. Do not run until the shared guarded slot is
allocated. It imports arithmetic helpers from the single-row expint checker,
not the manuscript SplitKernels evaluator.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import time
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
BASE_CHECKER = HERE / "h6_target_sigma_expint.py"
BASE_RECEIPT = HERE / "h6_target_sigma_expint.json"
OLD_SPLIT = HERE / "h6_target_sigma_direct.json"
TARGET_AGGREGATE = HERE / "h6_target_aggregate_replacement.json"
OUTPUT = HERE / "h6_all_quadratic_expint.json"

PINS = {
    "h6-low-degree-arithmetic.json": (ARITH, "b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771"),
    "h6-low-degree-moments-1586.json": (MOMENTS, "a7e65537a05389f11115a8cf64c186ead6b1dc4973a8c5f862f31a34fdeb40f1"),
    "h7-inherited-euler-12000.json": (TARGET, "b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f"),
    "analytic-replay-20260922.json": (ANALYTIC, "34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e"),
    "numerics_hecke_coeff_check.py": (COEFF_SOURCE, "3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329"),
    "h6_target_sigma_expint.py": (BASE_CHECKER, "1f600865d5cf895d2895c54b871a64763c11ae7d197722fb7e7b67eff8e1d6c0"),
    "h6_target_sigma_expint.json": (BASE_RECEIPT, "56aa4b9fddbe580d852119f79329635c06630d2833315857b581fe1aa0bb4e2f"),
    "h6_target_sigma_direct.json": (OLD_SPLIT, "d35c52ea39918684b39c456c1e1fd6f3cdad3b61e177f0eeea06c5457e7eff58"),
    "h6_target_aggregate_replacement.json": (TARGET_AGGREGATE, "35ec8d17c01f716663e9e7c7b64862413efd65cbae6807851b3d06536e360f27"),
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


def main() -> None:
    if not __debug__:
        raise RuntimeError("Python assertions are required")
    started = time.monotonic()
    for name, (path, expected) in PINS.items():
        actual = sha(path)
        if actual != expected:
            raise AssertionError(f"{name} SHA mismatch: {actual}")

    from flint import acb, arb, ctx
    import flint
    ctx.prec = 384
    one = load_module("h6_single_expint_helpers", BASE_CHECKER)
    arithmetic = json.loads(ARITH.read_text())
    moment_data = json.loads(MOMENTS.read_text())
    target = json.loads(TARGET.read_text())
    analytic = json.loads(ANALYTIC.read_text())
    base_result = json.loads(BASE_RECEIPT.read_text())
    old_split = json.loads(OLD_SPLIT.read_text())
    aggregate = json.loads(TARGET_AGGREGATE.read_text())

    if base_result.get("status") != "PASS target-sigma independent expint H6 AFE row":
        raise AssertionError("single-row expint reference receipt is not PASS")
    if old_split.get("status") != "FAIL target-sigma direct upper exceeds target row allowance":
        raise AssertionError("prior SplitKernels strict FAIL changed or missing")
    if not aggregate.get("status", "").startswith("PASS exact target mixed-quadratic aggregate replacement"):
        raise AssertionError("prior target aggregate PASS changed or missing")
    if target.get("sigma") != "12001/12000":
        raise AssertionError("wrong target sigma")
    target_rel = str(TARGET.relative_to(PUB))
    table_hash = analytic["printed_analytic_table_check"]["source_sha256"].get(target_rel)
    replay_hash = analytic["analytic_replay"]["replay_input_sha256"].get(target_rel)
    target_bound = (table_hash == sha(TARGET) and replay_hash == sha(TARGET)
                    and analytic.get("all_analytic_factors_reevaluated") is True)
    if not target_bound:
        raise AssertionError("target receipt is not hash-bound by consolidated analytic replay")

    sector = next(s for s in arithmetic["sectors"] if s["mask"] == 1586)
    if sector.get("dimension") != 2 or len(sector.get("rows", [])) != 32:
        raise AssertionError("expected the pinned 32-row degree-two sector")
    moments_by_twist = {r["twist"]: r for r in moment_data["rows"]}
    target_sector = next(s for s in target["sectors"]
                         if s.get("stage") == "H6-low" and s["mask"] == 1586)
    target_by_twist = {r["twist"]: r for r in target_sector["rows"]}
    if len(moments_by_twist) != 32 or len(target_by_twist) != 32:
        raise AssertionError("moment/target tables do not have the complete 32 twists")

    coeff_module = load_module("h6_batch_rank2_coefficients", COEFF_SOURCE)
    s = arb(12001) / 12000
    outputs = []
    total_coefficients = total_nonzero = max_n = 0
    comparison_failures = []
    consistency_failures = []
    for row in sector["rows"]:
        twist = int(row["twist"])
        mr = moments_by_twist[twist]
        tr = target_by_twist[twist]
        for key in ("twist", "conductor", "gamma", "root_number", "factor_multiplicity",
                    "bad_euler_denominators"):
            if row[key] != mr[key]:
                raise AssertionError(f"twist {twist}: arithmetic/moment mismatch at {key}")
        if (row.get("gamma") != [0, 1] or row.get("root_number") != 1
            or tr.get("kind") != "quadratic"
            or tr.get("status") != "PASS signed real AFE, exact root number+1"
            or tr.get("N") != mr.get("N")
            or tr.get("conductor") != row.get("conductor")
            or tr.get("multiplicity") != row.get("factor_multiplicity")):
            raise AssertionError(f"twist {twist}: target row identity/normalization mismatch")

        nmax = int(mr["N"])
        coefficients = [tuple(map(int, v)) for v in
                        coeff_module.rank2_first(row, sector, nmax)]
        if len(coefficients) != nmax:
            raise AssertionError(f"twist {twist}: coefficient length mismatch")
        vector = [(0, 0), *coefficients]
        coeff_hash = hashlib.sha256(json.dumps(vector).encode()).hexdigest()
        if coeff_hash != mr.get("signed_coefficients_sha256"):
            raise AssertionError(f"twist {twist}: full coefficient-vector hash mismatch")
        one.exact_bins(coefficients, mr["bins"], nmax)
        nonzero = sum(bool(re or im) for re, im in coefficients)
        expected_nonzero = sum(int(b["nonzero_count"]) for b in mr["bins"])
        if nonzero != expected_nonzero:
            raise AssertionError(f"twist {twist}: nonzero count mismatch")

        q = int(row["conductor"])
        t, primary_tail, dual_tail = one.elementary_tails(s, q, nmax)
        A, B = one.direct_expint_sums(coefficients, t, s)
        checks = {
            "A_center_consistency": one.contained_in_center_plus_error(
                A, tr["A_finite"]["real"], tr["one_side_interpolation_error"]),
            "B_center_consistency": one.contained_in_center_plus_error(
                B, tr["B_finite"]["real"], tr["one_side_interpolation_error"]),
        }
        signed = A + B
        error = primary_tail + dual_tail
        checks["positive_signed_lower"] = signed.lower() - error.upper() > 0
        bad = arb(1)
        for ptext, polynomial in row["bad_euler_denominators"].items():
            p = int(ptext)
            z = arb(p) ** (-s)
            value = acb(0)
            for j, (re, im) in enumerate(polynomial):
                value += acb(int(re), int(im)) * z ** j
            if not abs(value) > 0:
                raise AssertionError(f"twist {twist}: bad factor vanishes at p={p}")
            bad *= abs(value)
        checks["bad_multiplier_overlap"] = one.overlap(bad, tr["bad_multiplier_modulus"])
        modulus_upper = abs(signed).upper() + error.upper()
        removed_upper = (modulus_upper * bad).upper()
        log_upper = removed_upper.log().upper()
        direct_exact = one.endpoint_fraction(log_upper)
        target_exact = one.source_interval(tr["log_abs_L_S_upper"])[1]
        margin = target_exact - direct_exact
        compare = margin >= 0
        passed = compare and all(checks.values())
        if not compare:
            comparison_failures.append(twist)
        if not all(checks.values()):
            consistency_failures.append(twist)
        outputs.append({
            "twist": twist, "conductor": q, "N": nmax,
            "nonzero_coefficients": nonzero, "multiplicity": int(tr["multiplicity"]),
            "coefficient_vector_sha256": coeff_hash, "moment_bins_checked": len(mr["bins"]),
            "A_finite": one.encode_arb(A), "B_finite": one.encode_arb(B),
            "primary_tail_upper": one.encode_arb(primary_tail.upper()),
            "dual_tail_upper": one.encode_arb(dual_tail.upper()),
            "bad_multiplier": one.encode_arb(bad), "log_L_S_upper": one.encode_arb(log_upper),
            "target_log_L_S_upper": tr["log_abs_L_S_upper"],
            "direct_endpoint_exact": f"{direct_exact.numerator}/{direct_exact.denominator}",
            "target_endpoint_exact": f"{target_exact.numerator}/{target_exact.denominator}",
            "target_minus_direct_margin_exact": f"{margin.numerator}/{margin.denominator}",
            "target_minus_direct_margin_decimal": str(float(margin)),
            "consistency_checks": checks, "row_comparison_pass": compare,
            "overall_row_pass": passed,
        })
        total_coefficients += nmax
        total_nonzero += nonzero
        max_n = max(max_n, nmax)

    all_pass = not comparison_failures and not consistency_failures
    result = {
        "status": "PASS all 32 H6 quadratic rows by direct expint replay" if all_pass
                  else "FAIL one or more H6 quadratic row comparisons/consistency checks",
        "scope": "all 32 quadratic rows in H6 mask 1586 at target sigma 12001/12000; conditional finite row checks, not proof of H",
        "sigma": "12001/12000", "mask": 1586, "degree": 2, "gamma": [0, 1],
        "root_number_values": sorted({int(r["root_number"]) for r in sector["rows"]}),
        "row_count": len(outputs), "rows_with_strict_endpoint_failures": comparison_failures,
        "rows_with_consistency_failures": consistency_failures,
        "total_coefficients_reconstructed": total_coefficients,
        "maximum_cutoff_N": max_n, "total_nonzero_coefficients": total_nonzero,
        "generalized_expint_calls": 2 * total_nonzero,
        "precision_bits": ctx.prec, "python_flint_version": flint.__version__,
        "flint_version": flint.__FLINT_VERSION__, "target_receipt_bound_in_full_replay": target_bound,
        "target_receipt_sha256": sha(TARGET), "consolidated_analytic_replay_sha256": sha(ANALYTIC),
        "rows": outputs,
        "source_sha256": {name: expected for name, (_path, expected) in PINS.items()},
        "checker_sha256": sha(Path(__file__)), "seconds": time.monotonic() - started,
        "method": "Arb generalized expint with elementary d2 exponential tails; no SplitKernels import",
        "conditional_assumptions": [
            "all rows are the intended primitive entire degree-two factors with the pinned conductor and gamma_R(s)Gamma_R(s+1)",
            "all row root numbers are +1 and the stipulated conjugation-compatible functional equations give the signed real A+B formula",
            "the Dirichlet-series identity holds in a right half-plane and sufficient vertical growth/contour decay justifies the Mellin contour shift",
            "the listed bad Euler denominator polynomials are the complete removed local factors",
            "the global coefficient bound |a_n|<=d_2(n) holds for every row, including all infinite tails",
            "Arb/python-flint generalized expint and outward ball operations are sound",
        ],
        "limitations": [
            "coefficient hashes and finite bin identities do not prove the global coefficient bound or factor identities",
            "the independent kernel derivation still uses the Arb/FLINT backend and is conditional on contour-growth assumptions",
            "the check does not prove H and does not itself recompute the full 836-factor allowance",
            "the prior single-row SplitKernels FAIL and target aggregate PASS receipts are pinned separately and not changed",
        ],
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if not all_pass:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
