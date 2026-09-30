#!/usr/bin/env python3
"""Exact target-table substitution, preserving the direct row's strict FAIL.

Uses only Python's Fraction arithmetic. The pointwise target-sigma endpoint
is a valid upper under the conditional assumptions in its receipt, even
though it is a few final units above the frozen single-row endpoint.
"""
from __future__ import annotations

import hashlib
import json
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PUB = ROOT / "publication"
DIRECT = HERE / "h6_target_sigma_direct.json"
TARGET = PUB / "nonabelian-dyadic-lower-bound/research/h7-inherited-euler-12000.json"
FULL = ROOT / "lean-formalization/verification/external-zeta-20260922/analytic-replay-20260922.json"
OLD_DIRECT = HERE / "h6_mixed_quadratic_direct.json"
OLD_H6_AGGREGATE = HERE / "h6_aggregate_replacement.json"
OUTPUT = HERE / "h6_target_aggregate_replacement.json"

PINS = {
    "h6_target_sigma_direct.json": "d35c52ea39918684b39c456c1e1fd6f3cdad3b61e177f0eeea06c5457e7eff58",
    "h7-inherited-euler-12000.json": "b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f",
    "analytic-replay-20260922.json": "34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e",
    "h6_mixed_quadratic_direct.json": "5ad1872e87f6c9a823fc3d0ad9491b29807a8cfa9ff61b70335130f1a4caabcf",
    "h6_aggregate_replacement.json": "1df80e3c2ade0134178f35a6d7742f26930ba6d91bdd1b4e6c7ea52451175bf1",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dyadic(record: dict, side: str = "upper") -> Fraction:
    endpoint = record[side]
    return Fraction(int(endpoint["mantissa"])) * Fraction(2) ** int(endpoint["exponent"])


def main() -> None:
    started = time.monotonic()
    for name, expected in PINS.items():
        path = HERE / name if name.endswith(".json") and name.startswith("h6_") else None
        if name == "h7-inherited-euler-12000.json":
            path = TARGET
        elif name == "analytic-replay-20260922.json":
            path = FULL
        if path is None or digest(path) != expected:
            raise AssertionError(f"input hash mismatch: {name}")

    direct = json.loads(DIRECT.read_text())
    target = json.loads(TARGET.read_text())
    full = json.loads(FULL.read_text())
    old_direct = json.loads(OLD_DIRECT.read_text())
    old_h6 = json.loads(OLD_H6_AGGREGATE.read_text())
    assert direct["sigma"] == target["sigma"] == "12001/12000"
    assert direct["target_binding"]["target_receipt_in_consolidated_replay"]
    assert direct["status"] == "FAIL target-sigma direct upper exceeds target row allowance"
    assert direct["prior_off_sigma_evidence_preserved"]["direct_status"] == old_direct["status"]
    assert direct["prior_off_sigma_evidence_preserved"]["h6_aggregate_status"] == old_h6["status"]
    assert old_direct["status"] == "FAIL direct upper exceeds frozen allowance"
    assert old_h6["status"].startswith("PASS exact-rational H6 low-degree aggregate substitution")
    assert full["all_analytic_factors_reevaluated"] is True

    sector = next(s for s in target["sectors"]
                  if s.get("stage") == "H6-low" and s["mask"] == 1586)
    row = next(r for r in sector["rows"] if r["twist"] == 1)
    assert row["dimension"] == 2 and row["multiplicity"] == 1
    assert row["conductor"] == 240240 and row["N"] == 3922
    frozen_row_upper = dyadic(row["log_abs_L_S_upper"])
    direct_upper = Fraction(direct["comparison_diagnostic"]["direct_log_upper_exact_fraction"])
    assert frozen_row_upper == Fraction(direct["comparison_diagnostic"]["target_log_upper_exact_fraction"])
    row_delta = direct_upper - frozen_row_upper
    assert row_delta > 0

    table = full["printed_analytic_table_check"]
    group = next(g for g in table["groups"] if g["type"] == "mixed_quadratic")
    old_group_upper = Fraction(group["exact_input_upper"])
    rounded_group_allowance = Fraction(group["rational_allowance"])
    new_group_upper = old_group_upper + row_delta
    new_group_slack = rounded_group_allowance - new_group_upper
    assert new_group_slack > 0

    # A degree-two factor occurs once here. The exact normalized change is
    # d * delta / [K:Q] = 2 * delta / 16384 = delta / 8192.
    normalized_table_increment = row_delta * Fraction(2, 16384)
    old_final = Fraction(table["final_rational_upper"])
    ceiling = Fraction(table["ceiling"])
    # The group still rounds to the same rational allowance, so its published
    # rounded-table contribution and the final rational ceiling are unchanged.
    new_final = old_final
    assert old_final == Fraction("0.04216181893948094953138458")
    assert new_final < ceiling

    result = {
        "status": "PASS exact target mixed-quadratic aggregate replacement; strict row comparison remains FAIL",
        "scope": "one target-sigma degree-two row substituted into the exact mixed-quadratic group sum and checked against its rational allowance; not proof of H",
        "row_identity": {"mask": 1586, "twist": 1, "degree": 2, "multiplicity": 1,
                         "conductor": 240240, "N": 3922, "sigma": "12001/12000"},
        "strict_row_comparison": {
            "status": direct["status"],
            "direct_upper": str(direct_upper),
            "frozen_target_upper": str(frozen_row_upper),
            "direct_minus_frozen": str(row_delta),
            "direct_minus_frozen_decimal": f"{float(row_delta):.17g}",
            "interpolation_consistency": direct["consistency_checks"]["interpolation_debit_within_target"],
            "direct_interpolation_upper_minus_target_interpolation_upper": str(
                dyadic(direct["pointwise_interpolation_debit"])
                - dyadic(direct["target_interpolation_debit"])),
            "note": "The direct pointwise AFE upper remains an upper under its stated assumptions. The discrepancy is retained as a strict row FAIL, not hidden by aggregate substitution.",
        },
        "mixed_quadratic_exact_aggregate": {
            "factors": group["factors"],
            "old_exact_input_upper": str(old_group_upper),
            "row_upper_increment": str(row_delta),
            "new_exact_input_upper": str(new_group_upper),
            "rational_group_allowance": str(rounded_group_allowance),
            "new_exact_rounding_slack": str(new_group_slack),
            "strict_group_allowance_check": "PASS",
        },
        "full_table_effect": {
            "normalization": "degree * multiplicity / field_degree = 2/16384 = 1/8192",
            "normalized_exact_afe_increment": str(normalized_table_increment),
            "normalized_exact_afe_increment_decimal": f"{float(normalized_table_increment):.17g}",
            "rounded_mixed_quadratic_allowance_unchanged": True,
            "final_rational_upper_before": str(old_final),
            "final_rational_upper_after": str(new_final),
            "target_ceiling": str(ceiling),
            "ceiling_slack_after": str(ceiling - new_final),
            "target_exponent_claim_effect": "unchanged: the direct endpoint increases the exact group sum by this amount, but the 0.400886873183882259 group allowance still holds, so the published rational ceiling and 1.0418235 witness remain certified under the stated assumptions",
        },
        "source_sha256": {name: digest((HERE / name) if name.startswith("h6_") else
                                       (TARGET if name == "h7-inherited-euler-12000.json" else FULL))
                          for name in PINS},
        "script_sha256": digest(Path(__file__)),
        "seconds": time.monotonic() - started,
        "method": "Python standard-library fractions.Fraction over exact dyadic/rational receipt endpoints",
        "limitations": [
            "the original and target strict row comparisons remain FAIL",
            "this aggregate substitution is conditional on the direct row's factor identity, functional equation, global coefficient bound, conductor/gamma/root number, complete removed Euler factors, and tail/kernel assumptions",
            "this calculation does not prove H or independently verify the reused kernel proof",
        ],
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
