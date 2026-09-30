#!/usr/bin/env python3
"""Exact rational enclosure for the selected-prime-deleted chi_13 value.

Runs the checked primitive-period enclosure, then applies the manuscript's
S' correction as exact rational interval arithmetic. No floating-point value
enters either endpoint computation.
"""

from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import re
import subprocess
import sys

import genus13_lvalue_interval as primitive


ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
SCALE = primitive.SCALE
BASE_SCRIPT = Path(primitive.__file__).resolve()
BASE_SHA256 = "66b87a8d0967228dfd0fe0ece225bb0261438ecefba0eb821dbbd39c006b5460"
SOURCES = {
    "lean-formalization/UnitDistance/ZetaLunaConductorThirteenEulerRun20260922.lean":
        "6a2ae54fec9ee54bf780e126a431dad54316f58a8fbf416b1f1905637b127422",
    "lean-formalization/UnitDistance/ZetaLunaConductorThirteenImprimitiveEulerRun20260922.lean":
        "1b9b2e7b97d56f77860e7afc4be7cb6a831053a4f2d06fd9d7260ece44689ffd",
    "lean-formalization/UnitDistance/ZetaLunaConductorThirteenCommonLevelRun20260922.lean":
        "2ea6b772812ab2ac373a36cdc1cae0945878ba1fc95f6b2cd23b81be97ea6c42",
    "lean-formalization/UnitDistance/FixedZetaRetainedRationalFactorsAstra.lean":
        "19da60338e59cf662e90a8345bc7965536e865a62d20d08955fcab9b21012d93",
    "lean-formalization/UnitDistance/GenusDirichletPrimitiveRun20260920.lean":
        "6621fce9ac5c04a855c8e79d9ca0005d6c63a18cd87ca6b14e68bbc166fff99e",
}
OPTIONAL_SOURCES = {
    "lean-formalization/UnitDistance/SigmaCutAbsoluteGenus.lean":
        "33a4021d0b89643e1d79eff20f93aee9f5c5df548e9ec207c3ced0fef152235e",
    "lean-formalization/UnitDistance/Witness.lean":
        "56143fbf788d3d1a0e3fb0e8f4de76e5a8403b35fa74c22cfae43605ab7f8c81",
}
SELECTED_PRIMES = (2, 3, 5, 7, 11, 13, 17)
SELECTED_CHI = (-1, 1, -1, -1, -1, 0, 1)
EXPECTED_PRIMITIVE_LO = F(
    6626074990486226788823560073231467744757,
    10**40,
)
EXPECTED_PRIMITIVE_HI = F(
    662915167689496956311200034843303728921,
    10**39,
)


def floor_q(x: F) -> int:
    return x.numerator // x.denominator


def ceil_q(x: F) -> int:
    return -((-x.numerator) // x.denominator)


def parse_rational(text: str, label: str) -> F:
    match = re.search(rf"^{label} rational: (-?\d+)/(\d+)$", text, re.MULTILINE)
    assert match, f"missing {label} rational endpoint"
    return F(int(match.group(1)), int(match.group(2)))


def log_power_interval(p: int) -> tuple[F, F]:
    """Enclose p^(-12001/12000) via p^-1 exp(-log(p)/12000)."""
    log_lo, log_hi = primitive.log_integer_bounds(p)
    x_lo, x_hi = log_lo / 12_000, log_hi / 12_000
    assert 0 <= x_lo <= x_hi < 1
    exp_lo = primitive.exp_minus_taylor(x_hi, primitive.EXP_LOWER_DEGREE)
    exp_hi = primitive.exp_minus_taylor(x_lo, primitive.EXP_UPPER_DEGREE)
    lo, hi = exp_lo / p, exp_hi / p
    assert 0 < lo <= hi < F(1, p)
    return lo, hi


def main() -> None:
    assert sha256(BASE_SCRIPT.read_bytes()).hexdigest() == BASE_SHA256
    source_presence = {rel: (ROOT / rel).is_file() for rel in SOURCES}
    assert all(source_presence.values()) or not any(source_presence.values()), \
        "partial pinned Lean research-source checkout"
    if all(source_presence.values()):
        for rel, expected in SOURCES.items():
            assert sha256((ROOT / rel).read_bytes()).hexdigest() == expected, \
                f"source hash changed: {rel}"

        primitive_src = (ROOT / "lean-formalization/UnitDistance/ZetaLunaConductorThirteenEulerRun20260922.lean").read_text()
        imprimitive_src = (ROOT / "lean-formalization/UnitDistance/ZetaLunaConductorThirteenImprimitiveEulerRun20260922.lean").read_text()
        common_src = (ROOT / "lean-formalization/UnitDistance/ZetaLunaConductorThirteenCommonLevelRun20260922.lean").read_text()
        retained_src = (ROOT / "lean-formalization/UnitDistance/FixedZetaRetainedRationalFactorsAstra.lean").read_text()
        genus_primitive_src = (ROOT / "lean-formalization/UnitDistance/GenusDirichletPrimitiveRun20260920.lean").read_text()
        assert "def conductorThirteenPlaceEulerFactor" in primitive_src
        assert "(1 - genusPrimitiveCharacter conductorThirteenIndex p *" in primitive_src
        assert "DirichletCharacter.LFunction" in imprimitive_src
        assert "conductorThirteenPlaceEulerFactor s q)⁻¹" in imprimitive_src
        assert "conductorThirteenImprimitiveEulerValue_eq_commonLevelLFunction" in common_src
        assert "selectedPrimeValues_eq_commonGenusPrimeFactors" in common_src
        assert "selectedRationalPrimeSet : Finset Nat.Primes" in retained_src
        assert "commonGenusModulus_primeFactors" in genus_primitive_src
        assert "({2, 3, 5, 7, 11, 13, 17} : Finset ℕ)" in genus_primitive_src
        source_binding_mode = "pinned Lean research sources present; all source hashes and bindings matched"
    else:
        source_binding_mode = "fixture/source-hash-bound mode; all pinned Lean research sources absent"

    optional_paths = {}
    for rel in OPTIONAL_SOURCES:
        filename = rel.rsplit("/", 1)[-1]
        candidates = (
            HERE.parents[1] / "UnitDistance" / filename,
            ROOT / rel,
        )
        present = tuple(path for path in dict.fromkeys(candidates) if path.is_file())
        optional_paths[rel] = present

    optional_presence = {rel: bool(paths) for rel, paths in optional_paths.items()}
    for rel, expected in OPTIONAL_SOURCES.items():
        if optional_presence[rel]:
            for optional_path in optional_paths[rel]:
                optional_src = optional_path.read_text()
                assert sha256(optional_path.read_bytes()).hexdigest() == expected, \
                    f"optional source hash changed: {optional_path}"
                if rel.endswith("SigmaCutAbsoluteGenus.lean"):
                    assert "def selectedPrime (a : Fin 11) : Nat.Primes" in optional_src
                    assert "Witness.primes a" in optional_src
                else:
                    assert "def primes : Fin 11 → ℕ := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]" in optional_src
    optional_mode = ", ".join(rel.rsplit("/", 1)[-1] for rel, present in optional_presence.items() if present)
    if not optional_mode:
        optional_mode = "none present"

    # Re-run the exact-rational primitive checker and consume its exact output.
    run = subprocess.run(
        [sys.executable, str(BASE_SCRIPT)], check=True, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    primitive_lo = parse_rational(run.stdout, "lower")
    primitive_hi = parse_rational(run.stdout, "upper")
    assert (primitive_lo, primitive_hi) == (EXPECTED_PRIMITIVE_LO, EXPECTED_PRIMITIVE_HI)

    assert SELECTED_PRIMES == (2, 3, 5, 7, 11, 13, 17)
    assert tuple(primitive.legendre13(p) for p in SELECTED_PRIMES) == SELECTED_CHI

    correction_lo = F(1)
    correction_hi = F(1)
    factors = []
    for p, chi in zip(SELECTED_PRIMES, SELECTED_CHI):
        power_lo, power_hi = log_power_interval(p)
        if chi == 1:
            factor_lo, factor_hi = 1 - power_hi, 1 - power_lo
        elif chi == -1:
            factor_lo, factor_hi = 1 + power_lo, 1 + power_hi
        else:
            factor_lo = factor_hi = F(1)
        assert 0 < factor_lo <= factor_hi
        correction_lo *= factor_lo
        correction_hi *= factor_hi
        factors.append((p, chi, factor_lo, factor_hi))

    value_lo, value_hi = primitive_lo * correction_lo, primitive_hi * correction_hi
    correction_lo_out = F((correction_lo * SCALE).numerator // (correction_lo * SCALE).denominator, SCALE)
    correction_hi_out = F(ceil_q(correction_hi * SCALE), SCALE)
    value_lo_int = (value_lo * SCALE).numerator // (value_lo * SCALE).denominator
    value_hi_int = ceil_q(value_hi * SCALE)
    value_lo_out, value_hi_out = F(value_lo_int, SCALE), F(value_hi_int, SCALE)
    assert 0 < value_lo_out <= value_lo <= value_hi <= value_hi_out

    # The value lies below one. Enclose its real logarithm by applying the
    # existing atanh log enclosure to reciprocals in [1,2].
    assert value_hi_out < 1 and 1 / value_hi_out <= 2
    log_inv_lo, log_inv_lo_hi = primitive.atanh_log_bounds(1 / value_lo_out)
    log_inv_hi_lo, log_inv_hi = primitive.atanh_log_bounds(1 / value_hi_out)
    log_lo, log_hi = -log_inv_lo_hi, -log_inv_hi_lo
    log_lo_int = (log_lo * SCALE).numerator // (log_lo * SCALE).denominator
    log_hi_int = ceil_q(log_hi * SCALE)

    print(f"base primitive checker SHA-256: {BASE_SHA256}")
    print(f"source binding mode: {source_binding_mode}")
    print(f"optional provenance sources present and independently checked: {optional_mode}")
    print(f"source hashes: {SOURCES}")
    print(f"selected primes: {SELECTED_PRIMES}")
    print(f"chi13 values on selected primes: {SELECTED_CHI}")
    print(f"primitive L lower: {primitive_lo}")
    print(f"primitive L upper: {primitive_hi}")
    print(f"correction lower rational: {correction_lo_out}")
    print(f"correction upper rational: {correction_hi_out}")
    print(f"deleted value lower: {value_lo_out}")
    print(f"deleted value upper: {value_hi_out}")
    print(f"deleted value display (outward): [{primitive.fixed_decimal(floor_q(value_lo_out * 10**15), 15)}, {primitive.fixed_decimal(ceil_q(value_hi_out * 10**15), 15)}]")
    log_lower_out, log_upper_out = F(log_lo_int, SCALE), F(log_hi_int, SCALE)
    print(f"log modulus lower: {log_lower_out}")
    print(f"log modulus upper: {log_upper_out}")
    print(f"log modulus display (outward): [{primitive.fixed_decimal(floor_q(log_lower_out * 10**15), 15)}, {primitive.fixed_decimal(ceil_q(log_upper_out * 10**15), 15)}]")
    print("scope: exact-rational enclosure for primitive L times the selected S' deletion correction, identified with the common-level value by the pinned Lean theorem; no manuscript per-row allowance comparison")


if __name__ == "__main__":
    main()
