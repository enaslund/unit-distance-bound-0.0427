#!/usr/bin/env python3
"""Independent exact-rational audit of the selected exponent's terminal margin.

The numerical inequalities below are the endpoint theorems in six pinned Lean
sources. This checks their scalar assembly and coefficient directions without
calling Lean or reproducing its proof tactics.
"""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

if not __debug__:
    raise RuntimeError("Assertions are required; run without Python -O")


PROJECT = Path(__file__).resolve().parents[2]
SOURCE_HASHES = {
    "Target.lean": "65d3e569c5b97c52ba9fff5285d895e96e8a3fd5bf63f83c9045501679f3c2fb",
    "Witness.lean": "56143fbf788d3d1a0e3fb0e8f4de76e5a8403b35fa74c22cfae43605ab7f8c81",
    "LogBounds.lean": "6d3990f7581431dd6f0992df30e137302c620d60896763ccd8efd2e7e0ae5735",
    "NumericalReduction.lean": "8a2ecc9030f90b383471be7424b801bb0d27748baaa0aa4d7e2a5c7c2dbefb36",
    "FiniteFunctionalCertificate.lean": "db5a85db1791a10cac472af0706e68e8a1fc5ae47142bea114567b4393f9ff9a",
    "PairFunctionalSharperThresholdAstra.lean": "3d0e8a47cfed55c0c9daf09bea91aa82d97830fdcd83e413e553eceb867b5ad0",
}


def check() -> dict[str, object]:
    for name, expected in SOURCE_HASHES.items():
        path = PROJECT / "UnitDistance" / name
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"Source changed: {name}: {actual}")

    # Exact endpoint constants in the pinned sources above.
    increment = Q(83647, 2000000)
    theta_min = Q(4095, 8192)
    epsilon = Q(1, 10**9)
    old_ceiling = Q(42161819, 10**9)
    relaxed_ceiling = Q(42165819, 10**9)
    log_two_lower = Q(69314718055994530941, 10**20)
    log_two_upper = Q(69314718055994530942, 10**20)
    log_pi_lower = Q(114472988584940017413, 10**20)
    log_pi_upper = Q(114472988584940017415, 10**20)
    log_15015_upper = Q(9616804980418, 10**12)
    compact_lower = -Q(207166792766, 10**12)
    compact_upper = -Q(207166792765, 10**12)
    pair_lower = Q(1379633, 10**6)
    finite_profit_lower = Q(1033566922503, 10**12)

    assert increment == Q(2083647, 2000000) - 1
    assert relaxed_ceiling == old_ceiling + Q(4, 10**6)
    assert 0 < theta_min < Q(1, 2) and 0 < increment < Q(1, 2)
    assert log_two_lower <= log_two_upper
    assert log_pi_lower <= log_pi_upper
    assert compact_lower <= compact_upper

    # The slope of Witness.margin(theta) is
    # -log(pi) - 2 JCompact + JPair. Its lower endpoint is positive, so
    # theta_min is the worst admissible signature ratio.
    theta_slope_lower = -log_pi_upper - 2 * compact_upper + pair_lower
    assert theta_slope_lower > 0

    # Choose the lower/upper endpoint of each factor according to its signed
    # coefficient in Witness.margin(theta_min) - 4 epsilon. In particular,
    # logRD gets its upper endpoint, while the standalone log(2) gets its
    # lower endpoint. The coefficients of JCompact and JPair are positive.
    log_rd_upper = Q(9, 4) * log_two_upper + Q(1, 2) * log_15015_upper
    margin_lower = (
        finite_profit_lower
        - (Q(1, 2) - increment) * log_rd_upper
        - old_ceiling
        + (1 - increment) * log_two_lower
        + (1 - theta_min) * log_pi_lower
        + (1 - 2 * theta_min) * compact_lower
        + theta_min * pair_lower
        - 4 * epsilon
    )
    shifted_margin_lower = margin_lower - (relaxed_ceiling - old_ceiling)
    assert margin_lower > Q(4, 10**6)
    assert shifted_margin_lower > 0
    return {
        "status": "pass",
        "source_sha256": SOURCE_HASHES,
        "theta_slope_lower": str(theta_slope_lower),
        "margin_minus_four_epsilon_lower": str(margin_lower),
        "margin_minus_four_epsilon_lower_decimal": f"{float(margin_lower):.15g}",
        "margin_after_relaxed_ceiling_lower": str(shifted_margin_lower),
        "margin_after_relaxed_ceiling_lower_decimal": f"{float(shifted_margin_lower):.15g}",
        "scope": "Exact scalar recombination of named Lean endpoint bounds; no independent proof of the underlying integral, field, or zeta bounds.",
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
