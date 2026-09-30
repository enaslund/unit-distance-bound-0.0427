#!/usr/bin/env python3
"""Check one mixed quadratic Hecke row against an actual quartic field.

For unramified rational primes, the degree-one prime count in a monogenic
quartic field minus that in its quadratic subfield is the Artin trace of the
two-dimensional induction. The polynomial is derived from the selected
radicand and rational twist; no manuscript coefficient producer is called.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import numerics_hecke_coeff_check as coefficient_check


HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parents[1]
RESEARCH = PACKAGE.parent
SOURCE_DIR = RESEARCH / "publication/nonabelian-dyadic-lower-bound/research"
FIXTURE = HERE / "numerics_hecke_family_fixture.json"
OUT = HERE / "quartic_field_trace_check.json"
RAMIFIED = frozenset((2, 3, 5, 7, 11, 13))
COEFFICIENT_HELPER_SHA256 = "3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def primes_through(limit: int) -> list[int]:
    marks = bytearray(b"\x01") * (limit + 1)
    marks[:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if marks[p]:
            marks[p * p : limit + 1 : p] = b"\x00" * ((limit - p * p) // p + 1)
    return [p for p, prime in enumerate(marks) if prime]


def roots_over_quadratic_extension(p: int, d: int, a: int, b: int, c: int) -> tuple[int, int]:
    """Count roots of X²-a and X⁴+bX²+c over F_p[w]/(w²-d)."""
    def multiply(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
        return ((x[0] * y[0] + d * x[1] * y[1]) % p,
                (x[0] * y[1] + x[1] * y[0]) % p)

    quadratic = quartic = 0
    for x0 in range(p):
        for x1 in range(p):
            x2 = multiply((x0, x1), (x0, x1))
            if (x2[0] - a) % p == 0 and x2[1] == 0:
                quadratic += 1
            x4 = multiply(x2, x2)
            if (x4[0] + b * x2[0] + c) % p == 0 and (x4[1] + b * x2[1]) % p == 0:
                quartic += 1
    return quadratic, quartic


def source_bound_row() -> tuple[dict, dict, bool]:
    if digest(Path(coefficient_check.__file__)) != COEFFICIENT_HELPER_SHA256:
        raise ValueError("Imported coefficient helper hash changed")
    if digest(FIXTURE) != coefficient_check.FAMILY_FIXTURE_SHA256:
        raise ValueError("Family fixture hash changed")
    fixture = json.loads(FIXTURE.read_text())
    if fixture["source_sha256"] != coefficient_check.FAMILY_SOURCE_HASHES:
        raise ValueError("Family full-source hashes changed")
    record = fixture["families"]["mixed_quadratic"]
    row, sector = record["row"], record["sector"]
    arithmetic = SOURCE_DIR / record["arithmetic_source"]
    moments = SOURCE_DIR / record["moments_source"]
    available = arithmetic.is_file() and moments.is_file()
    if arithmetic.is_file() != moments.is_file():
        raise ValueError("Only one of the two full research source tables is present")
    if available:
        for path in (arithmetic, moments):
            if digest(path) != fixture["source_sha256"][path.name]:
                raise ValueError(f"Full source hash changed: {path.name}")
        full_arithmetic = json.loads(arithmetic.read_text())
        full_moments = json.loads(moments.read_text())
        exact_sector = next(s for s in full_arithmetic["sectors"] if s["mask"] == 1586)
        exact_row = next(r for r in full_moments["rows"] if r["twist"] == -1)
        if any(exact_sector.get(k) != v for k, v in sector.items()):
            raise ValueError("Fixture sector differs from full arithmetic source")
        if any(exact_row.get(k) != v for k, v in row.items()):
            raise ValueError("Fixture row differs from full moment source")
    return row, sector, available


def check() -> dict[str, object]:
    if not __debug__:
        raise RuntimeError("Assertions are required; run without Python -O")
    row, sector, full_source_compared = source_bound_row()
    if (sector["mask"], sector["dimension"], row["twist"]) != (1586, 2, -1):
        raise ValueError("Wrong mixed quadratic row")
    if sector["base_radicands"][1] != 1 or sector["eta_coefficients"][2:] != [0, 0]:
        raise ValueError("Selected row is not a quadratic-base radicand")
    a = int(sector["base_radicands"][0])
    x, y = map(int, sector["eta_coefficients"][:2])
    twist = int(row["twist"])
    # If u² = twist*(x+y√a), then u⁴ + b*u² + c = 0.
    b = -2 * twist * x
    c = twist * twist * (x * x - a * y * y)
    discriminant = 16 * c * (b * b - 4 * c) ** 2
    if (a, b, c, discriminant) != (-35, 34, 429, 16 * 429 * 560**2):
        raise ValueError("Unexpected actual quartic field polynomial")

    limit = int(row["N"])
    coefficients = coefficient_check.rank2_first(row, sector, limit)
    complete_vector = [(0, 0), *(tuple(v) for v in coefficients)]
    coefficient_hash = hashlib.sha256(json.dumps(complete_vector).encode()).hexdigest()
    if coefficient_hash != row["signed_coefficients_sha256"]:
        raise ValueError("Complete 981-coefficient row hash differs from source")

    good_primes = []
    trace_counts = {-2: 0, 0: 0, 2: 0}
    prime_square_checks = []
    for p in primes_through(limit):
        if p in RAMIFIED:
            continue
        if discriminant % p == 0:
            raise ValueError(f"Good prime {p} divides quartic discriminant")
        # At p not dividing the monic polynomial's discriminant, its roots
        # count degree-one prime ideals by Dedekind's factorization theorem.
        roots_quartic = sum((u**4 + b * u * u + c) % p == 0 for u in range(p))
        roots_quadratic = sum((u * u - a) % p == 0 for u in range(p))
        trace = roots_quartic - roots_quadratic
        actual = coefficients[p - 1]
        if actual != [trace, 0]:
            raise ValueError(f"Trace mismatch at p={p}: field {trace}, row {actual}")
        if trace not in trace_counts:
            raise ValueError(f"Unexpected trace {trace} at p={p}")
        trace_counts[trace] += 1
        good_primes.append(p)
        if p * p <= limit:
            d = next((x for x in range(2, p) if pow(x, (p - 1) // 2, p) == p - 1), None)
            if d is None:
                raise ValueError(f"No nonsquare found modulo p={p}")
            roots_f2, roots_k2 = roots_over_quadratic_extension(p, d, a, b, c)
            trace2 = roots_k2 - roots_f2
            if (trace * trace + trace2) % 2 != 0:
                raise ValueError(f"Odd prime-square coefficient numerator at p={p}")
            predicted = (trace * trace + trace2) // 2
            actual_square = coefficients[p * p - 1]
            if actual_square != [predicted, 0]:
                raise ValueError(
                    f"Prime-square mismatch at p={p}: field {predicted}, row {actual_square}"
                )
            prime_square_checks.append({
                "prime": p, "nonsquare": d, "trace_p": trace,
                "trace_p_squared_frobenius": trace2, "coefficient_p_squared": predicted,
            })
    if len(good_primes) < 100:
        raise ValueError("Too few good primes checked")
    result = {
        "status": "pass",
        "scope": "One selected mixed quadratic row: good-prime a_p traces and all eligible a_(p^2) through N=981 from direct quartic/quadratic polynomial root counts over F_p and F_(p^2); not a global Artin identity or an AFE check.",
        "fixture_sha256": digest(FIXTURE),
        "coefficient_helper_sha256": COEFFICIENT_HELPER_SHA256,
        "full_research_sources_compared": full_source_compared,
        "coefficient_vector_sha256": coefficient_hash,
        "mask": 1586,
        "twist": twist,
        "limit": limit,
        "quadratic_polynomial": f"X^2 - ({a})",
        "quartic_polynomial": f"X^4 + ({b})*X^2 + ({c})",
        "quartic_discriminant": discriminant,
        "excluded_ramified_primes": sorted(RAMIFIED),
        "selected_deleted_unramified_prime_17_checked": 17 in good_primes,
        "good_prime_count": len(good_primes),
        "prime_square_count": len(prime_square_checks),
        "prime_square_checks": prime_square_checks,
        "trace_counts": {str(k): v for k, v in trace_counts.items()},
    }
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
