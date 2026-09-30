#!/usr/bin/env python3
"""Independent exact-arithmetic checks of the 2026-09-22 zeta replay record.

This reads only the checked-in JSON replay output.  It deliberately does not
import or execute the manuscript's certificate/replay implementation.
"""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path


HERE = Path(__file__).resolve().parent
LEAN_ROOT = HERE.parents[1]
RECORD = LEAN_ROOT / "verification/external-zeta-20260922/analytic-replay-20260922.json"
EXPECTED_RECORD_SHA256 = "34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e"


def q(value: str | int) -> Fraction:
    return Fraction(value)


def dyadic(ball_endpoint: dict[str, object]) -> Fraction:
    return Fraction(int(ball_endpoint["mantissa"])) * Fraction(2) ** int(ball_endpoint["exponent"])


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> None:
    raw = RECORD.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == EXPECTED_RECORD_SHA256, f"replay record hash changed: {digest}")
    record = json.loads(raw)
    table = record["printed_analytic_table_check"]

    expected_groups = {
        "linear": (1, 128),
        "mixed_quadratic": (2, 256),
        "mixed_quartic": (4, 448),
        "pure_quartic": (4, 8),
        "mixed_octic": (8, 124),
    }
    group_upper_sum = Fraction(0)
    group_exact_sum = Fraction(0)
    for group in table["groups"]:
        label = group["type"]
        require(label in expected_groups, f"unexpected AFE group: {label}")
        require((group["degree"], group["factors"]) == expected_groups[label],
                f"wrong degree/count for {label}")
        exact_input = q(group["exact_input_upper"])
        allowance = q(group["rational_allowance"])
        slack = q(group["rounding_slack"])
        require(exact_input + slack == allowance,
                f"allowance does not equal exact input plus recorded slack for {label}")
        # The printed decimal allowance is an upper rational rounded at 18 places.
        require((allowance * 10**18).denominator == 1, f"unexpected allowance grid for {label}")
        require(allowance >= exact_input, f"allowance rounded down for {label}")
        group_exact_sum += exact_input
        group_upper_sum += allowance
    require(len(table["groups"]) == len(expected_groups), "missing AFE group")

    allowances = {name: q(value) for name, value in table["five_rational_allowances"].items()}
    require(set(allowances) == {"Y_upper", "bad_upper", "order_four_lower", "central_lower", "debit_upper"},
            "unexpected list of analytic allowances")
    y = q(table["dimension_weighted_table_Y"])
    require(y <= allowances["Y_upper"], "Y_upper is below the exact dimension-weighted table Y")
    assembled = (
        allowances["Y_upper"]
        + allowances["bad_upper"]
        - allowances["order_four_lower"]
        - allowances["central_lower"]
        + allowances["debit_upper"]
    )
    require(assembled == q(table["final_rational_upper"]),
            "five rational allowances do not assemble to final_rational_upper")
    require(Fraction(table["final_decimal_upper"]) == assembled,
            "printed decimal endpoint differs from exact rational assembly")
    ceiling = q(table["ceiling"])
    slack = q(table["ceiling_slack"])
    require(ceiling - assembled == slack > 0, "ceiling slack identity/sign failed")
    selected_lean_slack = Fraction(42165819, 10**9) - assembled
    require(selected_lean_slack > slack,
            "selected Lean ceiling slack should exceed the manuscript-threshold slack")

    analytic = record["analytic_replay"]
    fresh = analytic["fresh_C"]
    lower, upper = dyadic(fresh["lower"]), dyadic(fresh["upper"])
    require(lower <= assembled <= upper, "fresh dyadic enclosure misses rational table endpoint")
    require(q(table["original_assembled_upper"]) == upper,
            "table's original assembled upper differs from fresh replay upper endpoint")
    require(upper < ceiling, "dyadic upper endpoint does not lie below the manuscript ceiling")

    print("PASS independent exact rational analytic-table checks")
    print(f"record_sha256={digest}")
    print(f"afe_groups={len(expected_groups)} exact_input_sum={group_exact_sum}")
    print(f"afe_rounded_allowance_sum={group_upper_sum}")
    print(f"assembled={assembled}")
    print(f"dyadic_enclosure=[{lower}, {upper}]")
    print(f"ceiling_slack={slack}")
    print(f"selected_lean_ceiling_slack={selected_lean_slack}")
    print("scope=record arithmetic only; source AFE receipts and mathematical identifications not regenerated")


if __name__ == "__main__":
    main()
