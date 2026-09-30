#!/usr/bin/env python3
"""Exact Fraction substitution of all 32 H6 expint rows into the target table.

Source-ready arithmetic checker. Do not run until shared-slot allocation.
It consumes only pinned JSON receipts and the two aggregation source files;
it performs no analytic re-evaluation.
"""
from __future__ import annotations

import hashlib
import json
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PUB = REPO / "publication"
RESEARCH = PUB / "nonabelian-dyadic-lower-bound/research"
ARITH = RESEARCH / "h6-low-degree-arithmetic.json"
TARGET = RESEARCH / "h7-inherited-euler-12000.json"
FULL = REPO / "lean-formalization/verification/external-zeta-20260922/analytic-replay-20260922.json"
TABLE_ASSEMBLER = PUB / "unit-distance-1.0418235/certificates/check_analytic_table.py"
INHERITED_ASSEMBLER = RESEARCH / "h7-inherited-euler.py"
BATCH_CHECKER = HERE / "h6_all_quadratic_expint.py"
BATCH = HERE / "h6_all_quadratic_expint.json"
SINGLE = HERE / "h6_target_sigma_expint.json"
SPLIT_FAIL = HERE / "h6_target_sigma_direct.json"
SINGLE_AGG_PASS = HERE / "h6_target_aggregate_replacement.json"
OUTPUT = HERE / "h6_target_batch_aggregate.json"

PINS = {
    "h6-low-degree-arithmetic.json": (ARITH, "b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771"),
    "h7-inherited-euler-12000.json": (TARGET, "b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f"),
    "analytic-replay-20260922.json": (FULL, "34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e"),
    "check_analytic_table.py": (TABLE_ASSEMBLER, "768707a65d5b6bf2f1dc27ebf12e2cbc4a7ffbd87ecd5effb3acc2987387d662"),
    "h7-inherited-euler.py": (INHERITED_ASSEMBLER, "cb52db15386d204a92bf4b4f689742bb8e34e377df043170ed2a7c742e8ff0aa"),
    "h6_all_quadratic_expint.py": (BATCH_CHECKER, "060af68df4b7e1eb6dfba87e88ca13fa26cbccca16966c2c256b4fc8cd2116c3"),
    "h6_all_quadratic_expint.json": (BATCH, "54e9fe4921c92366da8644e27bd8d2217a04b678046dfa3c31701519b4c917ce"),
    "h6_target_sigma_expint.json": (SINGLE, "56aa4b9fddbe580d852119f79329635c06630d2833315857b581fe1aa0bb4e2f"),
    "h6_target_sigma_direct.json": (SPLIT_FAIL, "d35c52ea39918684b39c456c1e1fd6f3cdad3b61e177f0eeea06c5457e7eff58"),
    "h6_target_aggregate_replacement.json": (SINGLE_AGG_PASS, "35ec8d17c01f716663e9e7c7b64862413efd65cbae6807851b3d06536e360f27"),
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dyadic(record: dict, side: str = "upper") -> Fraction:
    item = record[side]
    return Fraction(int(item["mantissa"])) * Fraction(2) ** int(item["exponent"])


def main() -> None:
    if not __debug__:
        raise RuntimeError("Python assertions are required")
    started = time.monotonic()
    for label, (path, expected) in PINS.items():
        actual = sha(path)
        if actual != expected:
            raise AssertionError(f"{label} hash mismatch: {actual}")

    arithmetic = json.loads(ARITH.read_text())
    target = json.loads(TARGET.read_text())
    full = json.loads(FULL.read_text())
    batch = json.loads(BATCH.read_text())
    single = json.loads(SINGLE.read_text())
    split_fail = json.loads(SPLIT_FAIL.read_text())
    single_aggregate = json.loads(SINGLE_AGG_PASS.read_text())

    if batch.get("status") != "PASS all 32 H6 quadratic rows by direct expint replay":
        raise AssertionError("the pinned 32-row expint receipt is not PASS")
    if (batch.get("row_count") != 32 or batch.get("rows_with_strict_endpoint_failures")
        or batch.get("rows_with_consistency_failures")):
        raise AssertionError("the batch receipt is incomplete or has failures")
    if batch.get("target_receipt_bound_in_full_replay") is not True:
        raise AssertionError("the batch receipt does not assert verified full-replay target binding")
    if single.get("status") != "PASS target-sigma independent expint H6 AFE row":
        raise AssertionError("single-row expint PASS changed")
    if split_fail.get("status") != "FAIL target-sigma direct upper exceeds target row allowance":
        raise AssertionError("preserved SplitKernels strict row FAIL changed")
    if not single_aggregate.get("status", "").startswith(
            "PASS exact target mixed-quadratic aggregate replacement"):
        raise AssertionError("preserved one-row target aggregate PASS changed")
    if target.get("sigma") != "12001/12000" or full["all_analytic_factors_reevaluated"] is not True:
        raise AssertionError("wrong target sigma or consolidated analytic status")
    target_rel = str(TARGET.relative_to(PUB))
    table_source_hash = full["printed_analytic_table_check"]["source_sha256"].get(target_rel)
    replay_input_hash = full["analytic_replay"]["replay_input_sha256"].get(target_rel)
    if table_source_hash != sha(TARGET) or replay_input_hash != sha(TARGET):
        raise AssertionError("target inherited receipt is not explicitly bound in both full-replay maps")

    # The table assembler defines mixed-quadratic input as the sum of upper
    # endpoints of all inherited dimension-two sector log_L_S_sum records.
    # The inherited evaluator defines each H6 sector record as the sum of its
    # row endpoints weighted by factor_multiplicity. These pinned source files
    # establish which exact table component this local substitution updates.
    sector_rows = [s for s in arithmetic["sectors"] if s.get("mask") == 1586]
    if len(sector_rows) != 1 or sector_rows[0].get("dimension") != 2:
        raise AssertionError("expected one degree-two mask-1586 source sector")
    source_sector = sector_rows[0]
    target_sector = next(s for s in target["sectors"]
                         if s.get("stage") == "H6-low" and s.get("mask") == 1586)
    inherited_individual_factors = int(target_sector["individual_factors"])
    if target_sector.get("dimension") != 2:
        raise AssertionError("target sector is not degree two")

    if (len(source_sector.get("rows", [])) != 32
        or len(batch.get("rows", [])) != 32
        or len(target_sector.get("rows", [])) != 32):
        raise AssertionError("raw source, batch, or target row count is not 32")

    source_by_twist = {int(r["twist"]): r for r in source_sector["rows"]}
    batch_rows = {int(r["twist"]): r for r in batch["rows"]}
    target_rows = {int(r["twist"]): r for r in target_sector["rows"]}
    if len(source_by_twist) != 32 or set(batch_rows) != set(source_by_twist) or set(target_rows) != set(source_by_twist):
        raise AssertionError("source, direct replay, and inherited target twists differ")

    frozen_row_sum = Fraction(0)
    direct_row_sum = Fraction(0)
    sum_margin = Fraction(0)
    multiplicity_total = 0
    row_records = []
    for twist, source_row in sorted(source_by_twist.items()):
        direct = batch_rows[twist]
        frozen = target_rows[twist]
        mult = int(source_row["factor_multiplicity"])
        if (mult != int(frozen["multiplicity"])
            or int(direct["multiplicity"]) != mult
            or int(direct["conductor"]) != int(source_row["conductor"])
            or int(direct["N"]) != int(frozen["N"])):
            raise AssertionError(f"twist {twist}: row identity/multiplicity mismatch")
        if not direct["overall_row_pass"] or not direct["row_comparison_pass"]:
            raise AssertionError(f"twist {twist}: direct expint row no longer passes")
        direct_upper = Fraction(direct["direct_endpoint_exact"])
        frozen_upper = dyadic(frozen["log_abs_L_S_upper"])
        receipt_frozen = Fraction(direct["target_endpoint_exact"])
        if frozen_upper != receipt_frozen:
            raise AssertionError(f"twist {twist}: batch target endpoint does not match inherited receipt")
        margin = frozen_upper - direct_upper
        if margin <= 0 or Fraction(direct["target_minus_direct_margin_exact"]) != margin:
            raise AssertionError(f"twist {twist}: exact row margin mismatch/sign")
        frozen_row_sum += mult * frozen_upper
        direct_row_sum += mult * direct_upper
        sum_margin += mult * margin
        multiplicity_total += mult
        row_records.append({
            "twist": twist, "multiplicity": mult,
            "frozen_endpoint_exact": str(frozen_upper),
            "direct_expint_endpoint_exact": str(direct_upper),
            "target_minus_direct_margin_exact": str(margin),
        })
    if multiplicity_total != inherited_individual_factors:
        raise AssertionError("row multiplicities do not equal inherited sector factor count")

    sector_sum_upper = dyadic(target_sector["log_L_S_sum"])
    if frozen_row_sum > sector_sum_upper:
        raise AssertionError("row endpoint sum exceeds inherited sector's certified upper")
    if direct_row_sum > frozen_row_sum or frozen_row_sum - direct_row_sum != sum_margin:
        raise AssertionError("aggregate row substitution arithmetic mismatch")

    table = full["printed_analytic_table_check"]
    if table.get("sigma") != "12001/12000" or table.get("field_degree") != 16384:
        raise AssertionError("unexpected table abscissa/field degree")
    group = next(g for g in table["groups"] if g["type"] == "mixed_quadratic")
    if group.get("degree") != 2 or group.get("factors") != 256:
        raise AssertionError("unexpected mixed-quadratic group inventory")
    old_group = Fraction(group["exact_input_upper"])
    group_allowance = Fraction(group["rational_allowance"])
    old_group_slack = group_allowance - old_group
    if old_group_slack <= 0 or old_group_slack != Fraction(group["rounding_slack"]):
        raise AssertionError("frozen mixed-quadratic group allowance identity failed")

    # Replace the 32 endpoint sum while retaining the inherited sector's
    # existing outward summation slack. Thus group' = group + sum(direct-frozen).
    group_delta = direct_row_sum - frozen_row_sum
    new_group = old_group + group_delta
    new_group_slack = group_allowance - new_group
    if new_group_slack <= 0:
        raise AssertionError("updated mixed-quadratic group exceeds its allowance")

    # The inherited H target table weights this type by dimension 2 / 16384.
    # The rounded group allowance still holds, so preserve the established
    # rational table and five-allowance assembly exactly.
    five = {k: Fraction(v) for k, v in table["five_rational_allowances"].items()}
    final_before = Fraction(table["final_rational_upper"])
    final_after = (five["Y_upper"] + five["bad_upper"] - five["order_four_lower"]
                   - five["central_lower"] + five["debit_upper"])
    ceiling = Fraction(table["ceiling"])
    if final_after != final_before or final_after >= ceiling:
        raise AssertionError("inherited rational H target assembly changed or misses ceiling")
    normalized_exact_delta = Fraction(2, 16384) * group_delta
    if normalized_exact_delta >= 0:
        raise AssertionError("direct endpoint replacement did not lower the normalized group sum")
    table_y = Fraction(table["dimension_weighted_table_Y"])
    reconstructed_y = sum(
        int(g["degree"]) * Fraction(g["rational_allowance"])
        for g in table["groups"]
    ) / int(table["field_degree"])
    if table_y != reconstructed_y or table_y > five["Y_upper"]:
        raise AssertionError("dimension-weighted table Y identity/allowance failed")

    result = {
        "status": "PASS exact rational replacement of all 32 H6 quadratic endpoints; group allowance and inherited target assembly hold",
        "scope": "fraction-only substitution using all-32 expint row receipt into its H6 inherited sector, mixed-quadratic factor group, and existing inherited H-target rational assembly; conditional AFE premises are inherited, not proved here",
        "sigma": "12001/12000", "mask": 1586, "degree": 2,
        "row_count": len(row_records), "multiplicity_total": multiplicity_total,
        "row_margins_all_positive": True,
        "frozen_row_endpoint_sum_exact": str(frozen_row_sum),
        "direct_expint_row_endpoint_sum_exact": str(direct_row_sum),
        "sum_of_32_row_improvements_exact": str(sum_margin),
        "inherited_h6_sector_sum_upper_exact": str(sector_sum_upper),
        "inherited_sector_rounding_slack_over_row_endpoint_sum": str(sector_sum_upper - frozen_row_sum),
        "mixed_quadratic_group": {
            "factor_count": int(group["factors"]),
            "old_exact_input_upper": str(old_group),
            "replacement_delta_exact": str(group_delta),
            "new_exact_input_upper": str(new_group),
            "rational_allowance": str(group_allowance),
            "old_slack_exact": str(old_group_slack),
            "new_slack_exact": str(new_group_slack),
            "check": "PASS",
        },
        "inherited_H_target_assembly": {
            "normalization_of_group_delta": "2/16384",
            "normalized_exact_delta": str(normalized_exact_delta),
            "published_dimension_weighted_table_Y": str(table_y),
            "table_Y_allowance": str(five["Y_upper"]),
            "table_Y_identity": "PASS exact sum degree*group_allowance/field_degree",
            "published_rounded_group_allowance_unchanged": True,
            "final_rational_upper_before": str(final_before),
            "final_rational_upper_after": str(final_after),
            "ceiling": str(ceiling),
            "ceiling_slack": str(ceiling - final_after),
            "check": "PASS; same rational allowance keeps the published target assembly unchanged",
        },
        "preserved_method_specific_results": {
            "single_row_expint_status": single["status"],
            "single_row_expint_receipt_sha256": sha(SINGLE),
            "pointwise_splitkernels_status": split_fail["status"],
            "pointwise_splitkernels_receipt_sha256": sha(SPLIT_FAIL),
            "prior_single_row_aggregate_status": single_aggregate["status"],
            "prior_single_row_aggregate_receipt_sha256": sha(SINGLE_AGG_PASS),
        },
        "target_binding": {
            "inherited_receipt_sha256": sha(TARGET),
            "full_analytic_receipt_sha256": sha(FULL),
            "printed_table_source_sha256": table_source_hash,
            "analytic_replay_input_sha256": replay_input_hash,
            "all_analytic_factors_reevaluated": full["all_analytic_factors_reevaluated"],
            "target_receipt_in_consolidated_replay": batch["target_receipt_bound_in_full_replay"],
        },
        "rows": row_records,
        "source_sha256": {name: expected for name, (_path, expected) in PINS.items()},
        "checker_sha256": sha(Path(__file__)), "seconds": time.monotonic() - started,
        "method": "Python standard-library fractions.Fraction over exact dyadic endpoints; no Arb evaluation",
        "limitations": [
            "this checker proves only rational endpoint aggregation once the direct expint receipt is accepted",
            "it does not establish any row's factor identity, functional equation, Dirichlet-series contour conditions, coefficient/tail bound, or complete bad Euler factors",
            "it does not prove H; it reuses the inherited analytic receipt's other groups and allowances",
            "the prior pointwise SplitKernels strict row FAIL remains distinct and unchanged",
        ],
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
