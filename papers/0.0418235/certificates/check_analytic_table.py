#!/usr/bin/env python3
"""Check the direct degree-16384 analytic table using exact dyadic endpoints.

``verify(pub)`` takes the extracted supplementary ``publication`` directory.
This deliberately does not assert that reading stored intervals regenerates
their AFE proofs or integer moments: the enclosing replay supplies those
calculations and verifies the complete source/data manifest. This checker
independently assembles all factors into the five types used in the paper,
checks each displayed rational allowance, and proves the final rational
comparison with 0.042161819 without floating-point arithmetic.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path


F = Fraction
SIGMA = F(12001, 12000)
CEILING = F("0.042161819")
GROUPS = (
    ("linear", 1, 128, "7.337578130846530221"),
    ("mixed_quadratic", 2, 256, "0.400886873183882259"),
    ("mixed_quartic", 4, 448, "-0.046453348154273950"),
    ("pure_quartic", 4, 8, "0.058145052434373409"),
    ("mixed_octic", 8, 124, "-0.111176963043772737"),
)
ALLOWANCES = {
    "Y_upper": "0.000445355407103547",
    "bad_upper": "0.041727023150898786",
    "order_four_lower": "0.00003724741189544274807446",
    "central_lower": "0.00004201663320373563276702",
    "debit_upper": "0.00006870442657779491222606",
}
ROUNDED_FINAL = F("0.04216181893948094953138458")


def endpoint(record: dict, side: str) -> Fraction:
    item = record[side]
    return F(int(item["mantissa"])) * F(2) ** int(item["exponent"])


def interval(record: dict) -> tuple[Fraction, Fraction]:
    lo, hi = endpoint(record, "lower"), endpoint(record, "upper")
    if lo > hi:
        raise AssertionError("Reversed dyadic interval")
    return lo, hi


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def verify(pub: Path) -> dict:
    pub = Path(pub).resolve()
    research = pub / "nonabelian-dyadic-lower-bound/research"
    paths = {
        "inherited": research / "h7-inherited-euler-12000.json",
        "mixed": research / "h7-low-euler-12000.json",
        "pure": research / "h7-pure-euler-12000.json",
        "octic": research / "h7-octic-euler-12000.json",
        "euler": pub / "seven-dimensional-dyadic-lower-bound/certificates/euler.json",
    }
    data = {name: json.loads(path.read_text()) for name, path in paths.items()}
    for name, record in data.items():
        require(record["status"].startswith("PASS"), f"Unsuccessful {name} receipt")
        require(F(record["sigma"]) == SIGMA, f"Wrong abscissa in {name}")

    inherited, mixed, pure, octic, euler = (data[k] for k in paths)
    require(inherited["field_degree"] == 8192, "Unexpected intermediate degree")
    require(euler["field_degree"] == 16384, "Wrong complete field degree")
    require(len(inherited["sectors"]) == 63, "Incomplete intermediate factor partition")
    require(len(mixed["sectors"]) == 21, "Incomplete mixed quartic partition")
    require(len(pure["rows"]) == 8, "Incomplete pure quartic partition")
    require(len(octic["rows"]) == 78, "Incomplete octic evaluation partition")
    require(octic["sector_count"] == 42 and octic["individual_factors"] == 84,
            "Wrong new octic multiplicities")

    counts: Counter[int] = Counter()
    sums = {2: F(0), 4: F(0), 8: F(0)}
    masks = set()
    for sector in inherited["sectors"]:
        dimension = int(sector["dimension"])
        count = int(sector["individual_factors"])
        require(dimension in sums and count * dimension**2 == 128,
                "Incorrect intermediate Artin multiplicity")
        require(sector["mask"] not in masks, "Duplicate intermediate sector")
        masks.add(sector["mask"])
        counts[dimension] += count
        sums[dimension] += interval(sector["log_L_S_sum"])[1]
    require(counts == {2: 256, 4: 280, 8: 40}, "Wrong intermediate factor counts")
    require({int(k): v for k, v in inherited["individual_factor_counts"].items()}
            == dict(counts), "Intermediate count metadata disagree")

    new_counts = Counter()
    for sector in mixed["sectors"]:
        require(sector["dimension"] == 4 and sector["individual_factors"] == 8,
                "Incorrect mixed quartic multiplicity")
        require(sector["mask"] not in masks, "Duplicate completed sector")
        masks.add(sector["mask"])
        new_counts[4] += sector["individual_factors"]
    require(new_counts[4] == mixed["individual_degree4_factors"] == 168,
            "Wrong complete mixed quartic count")
    require(sum(row["factor_multiplicity"] for row in octic["rows"]) == 84,
            "Wrong octic pair count")
    require(all(row["gamma"] in ([0] * 4, [1] * 4)
                and row["root_number"] == 1 for row in pure["rows"]),
            "Wrong pure-quartic gamma/root-number data")
    require(Counter(tuple(row["gamma"]) for row in pure["rows"])
            == {(0, 0, 0, 0): 4, (1, 1, 1, 1): 4},
            "Wrong pure parity inventory")

    sums[4] += interval(mixed["new_degree4_log_L_S_upper"])[1]
    sums[8] += interval(octic["total_log_L_S_upper"])[1]
    counts[4] += 168
    counts[8] += 84
    actual_upper = {
        "linear": 128 * interval(inherited["genus_log_zeta_S_normalized"])[1],
        "mixed_quadratic": sums[2],
        "mixed_quartic": sums[4],
        "pure_quartic": interval(pure["total_log_L_S_upper"])[1],
        "mixed_octic": sums[8],
    }
    require(counts == {2: 256, 4: 448, 8: 124}, "Wrong final mixed-factor inventory")
    require(sum(dimension**2 * number for _, dimension, number, _ in GROUPS)
            == 16384, "Regular representation has wrong dimension")
    require(sum(number for _, _, number, _ in GROUPS) == 964,
            "Wrong irreducible count")

    rows = []
    weighted = F(0)
    for name, dimension, number, display in GROUPS:
        rounded = F(display)
        require(actual_upper[name] < rounded, f"Invalid upward rounding in {name}")
        weighted += dimension * rounded
        rows.append({"type": name, "degree": dimension, "factors": number,
                     "exact_input_upper": str(actual_upper[name]),
                     "rational_allowance": display,
                     "rounding_slack": str(rounded - actual_upper[name])})
    table_Y = weighted / 16384
    require(table_Y == F("0.00044535540710354679437255859375"),
            "Dimension-weighted factor table does not match the paper")
    values = {key: F(value) for key, value in ALLOWANCES.items()}
    require(table_Y < values["Y_upper"], "Invalid rounded Y bound")
    require(interval(euler["bad_restored"])[1] < values["bad_upper"],
            "Bad-prime allowance is too small")
    require(interval(euler["forced_saving"])[0] > values["order_four_lower"],
            "Order-four saving is too large")
    require(interval(euler["complement"]["complement"])[0] > values["central_lower"],
            "Central saving is too large")
    require(interval(euler["transfer_debit"])[1] < values["debit_upper"],
            "Transfer debit allowance is too small")
    require(euler["complement"]["genus_split_count"] == 293772662,
            "Wrong genus-split count")
    require(euler["complement"]["counts"] == [293705608, 291485548, 2220060],
            "Wrong census partition")
    require(len(euler["retained_forced_primes"]) == 45,
            "Wrong order-four correction count")
    require(interval(euler["transfer_slope"])[1]
            < F("0.824453118933538946712643997041"), "Invalid displayed slope")

    final = (values["Y_upper"] + values["bad_upper"]
             - values["order_four_lower"] - values["central_lower"]
             + values["debit_upper"])
    require(final == ROUNDED_FINAL < CEILING, "Final rational ceiling test failed")
    require(interval(euler["C"])[1] < CEILING, "Original outward assembly exceeds ceiling")
    return {
        "status": "PASS exact direct degree-16384 factor table and analytic ceiling",
        "scope": "Exact endpoint assembly of source-bound AFE receipts; the enclosing replay verifies or regenerates their mathematical inputs.",
        "sigma": str(SIGMA), "field_degree": 16384,
        "irreducible_factors": 964, "groups": rows,
        "dimension_weighted_table_Y": str(table_Y),
        "five_rational_allowances": ALLOWANCES,
        "final_rational_upper": str(final),
        "final_decimal_upper": "0.04216181893948094953138458",
        "ceiling": "0.042161819", "ceiling_slack": str(CEILING - final),
        "original_assembled_upper": str(interval(euler["C"])[1]),
        "source_sha256": {str(path.relative_to(pub)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in paths.values()},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("publication", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify(args.publication)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"])
    print("C <", result["final_decimal_upper"], "<", result["ceiling"])


if __name__ == "__main__":
    main()
