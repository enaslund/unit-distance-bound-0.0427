#!/usr/bin/env python3
"""Independent Arb replay of all 128 deleted quadratic genus factors.

The seven-bit mask selects [-1, 2, 3, 5, 7, 11, 13].  For its signed
squarefree radicand d, D = d if d = 1 (mod 4), and D = 4d otherwise.  We
construct the primitive quadratic character of fundamental discriminant D
in FLINT's Conrey numbering, check its entire period against an independently
implemented Kronecker symbol, then evaluate its Dirichlet L-value using Arb.

The script recomputes all finite selected-prime deletion factors and the sum
of their log moduli.  It reads the inherited certificate only for comparisons,
never for its numerical calculation.  It does not prove the analytic algorithm
inside FLINT or the Lean-to-Conrey character identity.
"""

import argparse
from hashlib import sha256
import json
from math import gcd, prod
from pathlib import Path
import sys
import time

from flint import acb, arb, ctx, dirichlet_char, fmpq


PACKAGE_ROOT = Path(__file__).resolve().parents[3]
RESEARCH_ROOT = PACKAGE_ROOT.parent
RADICANDS = (-1, 2, 3, 5, 7, 11, 13)
SELECTED_PRIMES = (2, 3, 5, 7, 11, 13, 17)
SIGMA_NUMERATOR = 12001
SIGMA_DENOMINATOR = 12000
LINEAR_ALLOWANCE = fmpq(7337578130846530221, 10**18)
ARCHIVED = RESEARCH_ROOT / "publication/nonabelian-dyadic-lower-bound/research/h7-inherited-euler-12000.json"
FIXTURE = Path(__file__).with_name("genus_comparison_fixture.json")
FIXTURE_SHA256 = "79a7a106b9b1aa2b233fb1c2fcbdae13e757ef513167a70aea50d8f4af3e21d4"
SOURCE_HASHES = {
    "lean-formalization/UnitDistance/GenusDirichletRowDataRun20260920.lean":
        "98710e5b067f57192358b66401c14cc59314bf6d734da81f79c47af5b09b86aa",
    "lean-formalization/UnitDistance/GenusDirichletConductorsActualRun20260920.lean":
        "00fdfac7a71cd2348463bb006e9accdf027ae669ccd5d5b4f3d74619a8e210a0",
    "lean-formalization/UnitDistance/GenusDirichletFactorsRun20260920.lean":
        "0583e086cd5194b1fd87674fa2905666c6980ebf946939294ced31c80109f728",
    "lean-formalization/UnitDistance/GenusDirichletPrimitiveActualRun20260920.lean":
        "d277084222814aad0f4660c38e334d91d083cfbc82ad183affb1912fb0811ad4",
}
ARCHIVED_SHA256 = "b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f"


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def jacobi(a, odd_n):
    """Jacobi symbol (a/odd_n), for positive odd denominator."""
    check(odd_n > 0 and odd_n % 2 == 1, "Jacobi denominator must be positive odd")
    a %= odd_n
    sign = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if odd_n % 8 in (3, 5):
                sign = -sign
        a, odd_n = odd_n, a
        if a % 4 == 3 and odd_n % 4 == 3:
            sign = -sign
        a %= odd_n
    return sign if odd_n == 1 else 0


def kronecker_positive_denominator(D, n):
    """Kronecker (D/n), n>=1, using (D/2) and quadratic reciprocity."""
    check(n >= 1, "positive Kronecker denominator required")
    sign = 1
    while n % 2 == 0:
        if D % 2 == 0:
            return 0
        if D % 8 in (3, 5):
            sign = -sign
        n //= 2
    return sign * jacobi(D, n)


def discriminant(mask):
    d = prod(RADICANDS[j] for j in range(7) if (mask >> j) & 1)
    return d if d % 4 == 1 else 4 * d


def conrey_number(D):
    """CRT of -1 at odd conductor primes and the quadratic 2-adic label."""
    q = abs(D)
    if q == 1:
        return 1
    if q % 2:
        return q - 1
    odd = q
    while odd % 2 == 0:
        odd //= 2
    two_part = q // odd
    if two_part == 4:
        return q - 1
    check(two_part == 8, f"unexpected 2-part {two_part} of conductor {q}")
    two_label = 5 if (D // 8) % 4 == 1 else 3
    multiplier = ((two_label + 1) * pow(odd, -1, 8)) % 8
    label = (odd * multiplier - 1) % q
    check(1 <= label < q and gcd(label, q) == 1, f"invalid Conrey label for D={D}")
    return label


def dyadic_endpoint(endpoint):
    numerator = int(endpoint["mantissa"])
    exponent = int(endpoint["exponent"])
    return fmpq(numerator * (2**max(0, exponent)), 2**max(0, -exponent))


def inside_archived_interval(value, stored, label):
    lower = dyadic_endpoint(stored["lower"])
    upper = dyadic_endpoint(stored["upper"])
    check(arb(lower) < value < arb(upper), f"{label} misses archived dyadic enclosure")


def load_comparison():
    check(sha256(FIXTURE.read_bytes()).hexdigest() == FIXTURE_SHA256,
          "portable comparison fixture changed")
    fixture = json.loads(FIXTURE.read_text())
    check(fixture["schema"] == "unit-distance-genus-comparison-fixture-v1",
          "comparison fixture schema changed")
    check(fixture["sigma"] == "12001/12000", "comparison sigma changed")
    check(fixture["source_sha256"] == SOURCE_HASHES, "source hashes changed")
    check(fixture["archived_sha256"] == ARCHIVED_SHA256,
          "archived comparison hash changed")
    check(len(fixture["genus_rows"]) == 128, "comparison row count changed")

    verified_sources = []
    for relative, expected_hash in SOURCE_HASHES.items():
        candidates = (RESEARCH_ROOT / relative,
                      PACKAGE_ROOT / relative.removeprefix("lean-formalization/"))
        paths = [path for path in candidates if path.is_file()]
        for path in paths:
            check(sha256(path.read_bytes()).hexdigest() == expected_hash,
                  f"Lean source hash changed: {path}")
        if paths:
            verified_sources.append(relative)

    archived_present = ARCHIVED.is_file()
    if archived_present:
        check(sha256(ARCHIVED.read_bytes()).hexdigest() == ARCHIVED_SHA256,
              "inherited comparison data changed")
        archived = json.loads(ARCHIVED.read_text())
        check(archived["sigma"] == fixture["sigma"], "archived sigma changed")
        check(archived["genus_log_zeta_S_normalized"] ==
              fixture["genus_log_zeta_S_normalized"],
              "fixture aggregate differs from archived data")
        for index, (original, compact) in enumerate(zip(archived["genus_rows"],
                                                         fixture["genus_rows"])):
            projected = {key: original[key] for key in
                         ("mask", "D", "conrey_number", "L", "log_L_S")}
            check(projected == compact,
                  f"fixture row {index} differs from archived data")
        check(len(archived["genus_rows"]) == 128, "archived row count changed")
    return fixture, verified_sources, archived_present


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=128,
                        help="development prefix; the full certificate uses 128")
    args = parser.parse_args()
    check(1 <= args.limit <= 128, "limit must be in 1..128")
    archived, verified_sources, archived_present = load_comparison()
    archived_rows = archived["genus_rows"]

    # The archived dyadic endpoints were computed at 384 bits and are much
    # tighter than their short decimal display strings.  Evaluate at 512 bits
    # so interval inclusion tests have room for a genuinely independent run.
    ctx.prec = 512
    sigma_real = arb(SIGMA_NUMERATOR) / SIGMA_DENOMINATOR
    sigma_complex = acb(SIGMA_NUMERATOR) / SIGMA_DENOMINATOR
    start = time.monotonic()
    total_log = arb(0)
    rows = []
    periodic_values_checked = 0
    for mask in range(args.limit):
        D = discriminant(mask)
        q = abs(D)
        label = conrey_number(D)
        row = archived_rows[mask]
        check(row["mask"] == mask and row["D"] == D and
              row["conrey_number"] == label,
              f"inherited row label mismatch at mask {mask}")
        character = dirichlet_char(q, label)
        check(character.conductor() == q and character.is_real(),
              f"wrong conductor or nonreal character at mask {mask}")
        check(character.order() <= 2, f"nonquadratic Conrey character at mask {mask}")
        # Validate the entire finite period, not only a small generator sample.
        for n in range(1, q + 1):
            expected = kronecker_positive_denominator(D, n)
            check(character(n) == expected,
                  f"Kronecker/Conrey coefficient mismatch: mask={mask}, n={n}")
        periodic_values_checked += q

        primitive = character.l(sigma_complex)
        check(primitive.imag == 0 and primitive.real > 0,
              f"primitive value not positive real at mask {mask}")
        correction = acb(1)
        for p in SELECTED_PRIMES:
            correction *= 1 - character(p) * (arb(p) ** (-sigma_real))
        deleted = primitive * correction
        check(deleted.imag == 0 and deleted.real > 0,
              f"deleted value not positive real at mask {mask}")
        log_deleted = deleted.real.log()
        inside_archived_interval(primitive.real, row["L"], f"L row {mask}")
        inside_archived_interval(log_deleted, row["log_L_S"],
                                 f"deleted log row {mask}")
        total_log += log_deleted
        rows.append({"mask": mask, "D": D, "conrey_number": label,
                     "conductor": q, "primitive_L": str(primitive.real),
                     "deleted_value": str(deleted.real),
                     "deleted_log": str(log_deleted)})

    result = {
        "status": "pass",
        "scope": "Independent Arb L-value and selected-prime deletion replay for actual mask-derived quadratic characters; comparison data used only after calculation. Analytic algorithm, Lean-to-Conrey identity, other factor families, and H are outside this check.",
        "source_sha256": SOURCE_HASHES,
        "source_hashes_verified_in_this_run": verified_sources,
        "lean_sources_absent_from_this_run":
            sorted(set(SOURCE_HASHES) - set(verified_sources)),
        "inherited_comparison_sha256": ARCHIVED_SHA256,
        "inherited_archive_verified_in_this_run": archived_present,
        "portable_comparison_fixture_sha256": FIXTURE_SHA256,
        "comparison_mode": "archive_and_fixture" if archived_present else "fixture_only",
        "python": sys.version.split()[0],
        "flint": __import__("flint").__version__,
        "precision_bits": ctx.prec,
        "sigma": "12001/12000",
        "masks_checked": args.limit,
        "periodic_coefficients_checked": periodic_values_checked,
        "total_conductor": sum(row["conductor"] for row in rows),
        "all_row_values_inside_pinned_fixture_intervals": True,
        "genus_log_sum": str(total_log),
        "wall_seconds": round(time.monotonic() - start, 3),
        "rows": rows,
    }
    if args.limit == 128:
        check(periodic_values_checked == 677376, "conductor-period sum changed")
        check(total_log / 128 < arb(dyadic_endpoint(
            archived["genus_log_zeta_S_normalized"]["upper"])),
            "direct aggregate misses inherited normalized receipt upper")
        check(total_log < arb(LINEAR_ALLOWANCE),
              "direct aggregate exceeds rounded linear allowance")
        result["aggregate_below_inherited_receipt_upper"] = True
        result["aggregate_below_linear_allowance"] = True
        result["linear_allowance"] = "7337578130846530221/10^18"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"PASS {args.limit} genus masks; checked {periodic_values_checked} period values")
    print(f"direct genus log sum: {total_log}")
    if args.limit == 128:
        print("below inherited dyadic upper and linear allowance: yes")


if __name__ == "__main__":
    main()
