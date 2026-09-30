#!/usr/bin/env python3
"""Exact-rational H6 aggregate substitution for one direct AFE endpoint.

This script does not change the frozen row check: the direct row endpoint
remains a FAIL against its printed allowance. It separately substitutes that
endpoint into the H6 low-degree weighted sum and checks the published cap.
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
RESEARCH = ROOT / "publication/nonabelian-dyadic-lower-bound/research"
AUDIT = ROOT / "lean-formalization/verification/sol-luna-20260923/numerical-audit"
EULER_PATH = RESEARCH / "h6-low-degree-euler-6000.json"
DIRECT_PATH = AUDIT / "h6_mixed_quadratic_direct.json"
OUTPUT_PATH = AUDIT / "h6_aggregate_replacement.json"
EXPECTED_INPUT_HASHES = {
    "h6-low-degree-euler-6000.json": "bd9c19c7b128a17fd1ea84afae062f812bb2915b4fe2dfea813bfb074496d459",
    "h6_mixed_quadratic_direct.json": "5ad1872e87f6c9a823fc3d0ad9491b29807a8cfa9ff61b70335130f1a4caabcf",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def interval_upper(value: dict) -> Fraction:
    """Decode the exact dyadic upper endpoint used by the frozen receipt."""
    endpoint = value["upper"]
    mantissa = int(endpoint["mantissa"])
    exponent = int(endpoint["exponent"])
    return Fraction(mantissa) * Fraction(2) ** exponent


def main() -> None:
    assert sha256(EULER_PATH) == EXPECTED_INPUT_HASHES[EULER_PATH.name]
    assert sha256(DIRECT_PATH) == EXPECTED_INPUT_HASHES[DIRECT_PATH.name]
    source = json.loads(EULER_PATH.read_text())
    direct = json.loads(DIRECT_PATH.read_text())
    assert source["sigma"] == direct["sigma"] == "6001/6000"
    assert direct["sector_mask"] == 1586 and direct["twist"] == 1
    assert direct["degree"] == 2 and direct["conductor"] == 240240
    assert direct["N"] == 3922 and direct["nonzero_coefficients"] == 562

    # Confirm exactly one degree-two input row represents this direct row.
    matches = []
    for sector in source["sectors"]:
        for row in sector["rows"]:
            if (row.get("mask"), row.get("twist"), row.get("dimension"),
                    row.get("conductor"), row.get("N")) == (1586, 1, 2, 240240, 3922):
                matches.append(row)
    assert len(matches) == 1 and matches[0]["multiplicity"] == 1

    old_row = Fraction(direct["comparison_diagnostic"]["printed_log_upper_exact_fraction"])
    direct_row = Fraction(direct["comparison_diagnostic"]["direct_log_upper_exact_fraction"])
    row_delta = direct_row - old_row
    assert row_delta > 0

    degree2_sum = interval_upper(source["degree2_log_sum_upper"])
    degree4_sum = interval_upper(source["degree4_log_sum_upper"])
    frozen_h6 = interval_upper(source["H6_normalized_contribution_upper"])
    # There are 32 individual degree-two factors. This row occurs once, and
    # the Artin dimension weight is 2, so its normalized increment is
    # (2 * row_delta) / 8192 = row_delta / 4096.
    changed_degree2_sum = degree2_sum + row_delta
    changed_h6 = (2 * changed_degree2_sum + 4 * degree4_sum) / 8192
    baseline_from_degree_sums = (2 * degree2_sum + 4 * degree4_sum) / 8192
    # The separately serialized normalized endpoint can differ from the
    # recombination by outward-rounding at its final dyadic projection.
    aggregation_rounding_gap = baseline_from_degree_sums - frozen_h6

    cap = Fraction(-1216249516141204767, 25000000000000000000000)
    assert changed_h6 < cap

    # The consolidated five-family receipt uses a different sigma. Record the
    # mismatch explicitly; it is not the target of this substitution check.
    aggregate_path = ROOT / "lean-formalization/verification/external-zeta-20260922/analytic-replay-20260922.json"
    aggregate = json.loads(aggregate_path.read_text())
    five_family_sigma = aggregate["analytic_replay"].get("sigma")
    result = {
        "status": "PASS exact-rational H6 low-degree aggregate substitution; frozen row endpoint remains FAIL",
        "scope": "H6 low-degree aggregate only, at sigma 6001/6000; not global H and not the five-family aggregate",
        "row": {"mask": 1586, "twist": 1, "degree": 2, "conductor": 240240,
                "N": 3922, "multiplicity": 1, "nonzero_coefficients": 562},
        "row_comparison": {
            "status": direct["status"],
            "frozen_allowance": str(old_row),
            "direct_upper": str(direct_row),
            "direct_minus_frozen": str(row_delta),
            "direct_minus_frozen_decimal": f"{float(row_delta):.17g}",
            "diagnosis": "pointwise replay upper is slightly larger than frozen moment-contraction allowance; direct replay JSON retains FAIL",
        },
        "aggregate_replacement": {
            "degree2_sum_frozen": str(degree2_sum),
            "degree2_sum_replaced": str(changed_degree2_sum),
            "degree4_sum": str(degree4_sum),
            "normalized_weight_increment": str(row_delta / 4096),
            "normalized_weight_increment_decimal": f"{float(row_delta / 4096):.17g}",
            "H6_normalized_frozen_receipt": str(frozen_h6),
            "H6_normalized_from_frozen_degree_sums": str(baseline_from_degree_sums),
            "final_projection_rounding_gap": str(aggregation_rounding_gap),
            "H6_normalized_replaced": str(changed_h6),
            "H6_published_cap": str(cap),
            "cap_minus_replaced_exact": str(cap - changed_h6),
            "cap_minus_replaced_decimal": f"{float(cap - changed_h6):.17g}",
            "strict_cap_check": "PASS",
        },
        "sigma": "6001/6000",
        "five_family_receipt_sigma": five_family_sigma,
        "five_family_comparison": "not checked by this substitution: the consolidated five-family analytic receipt is at sigma 12001/12000, so the H6 row at 6001/6000 cannot be inserted into it directly",
        "source_sha256": {
            str(EULER_PATH.relative_to(ROOT)): sha256(EULER_PATH),
            str(DIRECT_PATH.relative_to(ROOT)): sha256(DIRECT_PATH),
            str(aggregate_path.relative_to(ROOT)): sha256(aggregate_path),
        },
        "method": "Python standard-library fractions.Fraction; exact dyadic receipt endpoints and direct row fraction; one degree-two factor multiplicity, Artin weight 2, field-degree denominator 8192",
        "limitations": [
            "This exact arithmetic only propagates a finite row upper into the H6 low-degree aggregate.",
            "It does not repair or overturn the direct-versus-frozen row FAIL.",
            "The direct endpoint remains conditional on its analytic row and coefficient assumptions, and reuses the pinned SplitKernels/Arb backend.",
            "No conclusion about the consolidated five-family receipt follows because its sigma differs.",
        ],
    }
    OUTPUT_PATH.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
