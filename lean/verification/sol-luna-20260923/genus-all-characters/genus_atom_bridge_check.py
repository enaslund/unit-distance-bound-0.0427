#!/usr/bin/env python3
"""Finite exact comparison of mask-local atoms with the D-Kronecker character.

This stdlib-first checker covers every residue in the primitive conductor
period for all 128 seven-bit masks.  It checks the explicit 2-primary atom
times the selected odd Legendre atoms against an independently implemented
Kronecker symbol.  If python-flint is installed, it also checks the full
period against the Conrey character selected by genus_full_direct.py.

This is finite arithmetic evidence, not a Lean theorem or a proof of the
analytic correctness of FLINT's L-value algorithm.
"""

from hashlib import sha256
import argparse
import json
from math import gcd, prod
from pathlib import Path
import runpy
import sys
import time


HERE = Path(__file__).resolve().parent
CHECKOUT_LAYOUT = HERE.parents[2].name == "lean-formalization"
REPO_ROOT = HERE.parents[3] if CHECKOUT_LAYOUT else HERE.parents[2]
RADICANDS = (-1, 2, 3, 5, 7, 11, 13)
ODD_ATOM_PRIMES = (3, 5, 7, 11, 13)
EXPECTED_PERIOD_SUM = 677376
REFERENCE_SCRIPT = (
    "lean-formalization/verification/sol-luna-20260923/"
    "genus-all-characters/genus_full_direct.py"
)
FACTOR_NOTE = (
    "lean-formalization/verification/sol-luna-20260923/"
    "genus-all-characters/kronecker-factorization-argument.md"
)

# These hashes bind the finite computation to the row convention, local atom
# construction, primitive assembly, reciprocity lemmas, and reference Conrey
# label routine inspected for this check.
SOURCE_SHA256 = {
    "lean-formalization/UnitDistance/GenusDirichletRowDataRun20260920.lean":
        "98710e5b067f57192358b66401c14cc59314bf6d734da81f79c47af5b09b86aa",
    "lean-formalization/UnitDistance/GenusDirichletConductorsRun20260920.lean":
        "da1f113fb627a0e64651d1b5998f453f7d0e452771ea0a1f18ada752ca9b3a77",
    "lean-formalization/UnitDistance/GenusDirichletConductorsActualRun20260920.lean":
        "00fdfac7a71cd2348463bb006e9accdf027ae669ccd5d5b4f3d74619a8e210a0",
    "lean-formalization/UnitDistance/GenusDirichletPrimitiveRun20260920.lean":
        "6621fce9ac5c04a855c8e79d9ca0005d6c63a18cd87ca6b14e68bbc166fff99e",
    "lean-formalization/UnitDistance/GenusDirichletPrimitiveActualRun20260920.lean":
        "d277084222814aad0f4660c38e334d91d083cfbc82ad183affb1912fb0811ad4",
    "lean-formalization/UnitDistance/GenusDirichletDatumCompositionRun20260920b.lean":
        "9302950c7b0a465624236ce334820508732d6fa9522c504f3b61ceb89da2310e",
    "lean-formalization/UnitDistance/GenusDirichletRootNumbersActualRun20260920b.lean":
        "44c6cdc22b22b71390493d2cf8e237eabdffcc96f05120f99e39dd84dec72e21",
    "lean-formalization/UnitDistance/GenusDirichletTwoPrimaryGaussRun20260920b.lean":
        "98f86a062f6bc8da34b1aa2dd0507927bd936d1bd8c373afc7f480c1be17a4b2",
    "lean-formalization/UnitDistance/GenusDirichletReciprocityRun20260920.lean":
        "d270209e203897aa51cdc4065128d6f1556d15df2b9b713266fb50fc0645fb98",
    "lean-formalization/UnitDistance/GenusDirichletCharacterBridge.lean":
        "399a31a76e810e985ad291211f3695e5b2a212880ae121176cb563f227d41da7",
    REFERENCE_SCRIPT:
        "24f0a4cfa2b6eb4b3ad390ce62571b1a23b7978d6d660733e1328dd1b1f299e5",
    FACTOR_NOTE:
        "066ae9d25aff094abcae2820d6524cd59ce6037e5532731501b1c1327677a3b7",
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256_file(path):
    return sha256(path.read_bytes()).hexdigest()


def verify_sources():
    actual = {}
    absent = []
    for relative, expected in SOURCE_SHA256.items():
        if relative in (REFERENCE_SCRIPT, FACTOR_NOTE):
            path = HERE / Path(relative).name
        else:
            path = REPO_ROOT / relative if CHECKOUT_LAYOUT else None
        if path is None or not path.is_file():
            # Candidate packages carry the checker and references, but may
            # omit the research Lean sources. Verify every Lean pin that is
            # present; never silently omit the local checker/note references.
            if relative.startswith("lean-formalization/UnitDistance/"):
                absent.append(relative)
                continue
            require(False, f"missing required pinned input: {relative}")
        digest = sha256_file(path)
        require(digest == expected,
                f"pinned input changed: {relative} expected={expected} actual={digest}")
        actual[relative] = digest
    return {"verified": actual, "absent_lean_sources": absent}


def discriminant(mask):
    d = prod(RADICANDS[j] for j in range(7) if (mask >> j) & 1)
    return d if d % 4 == 1 else 4 * d


def legendre(n, q):
    """Legendre (n/q) by Euler's criterion; q is one of 3,5,7,11,13."""
    residue = pow(n % q, (q - 1) // 2, q)
    if residue == 0:
        return 0
    if residue == 1:
        return 1
    require(residue == q - 1, f"Euler criterion failed: n={n}, q={q}")
    return -1


def two_primary_atom(mask, n):
    """Return T_m(n) from the (b,r) table in the paper-level note."""
    a = (mask >> 0) & 1
    b = (mask >> 1) & 1
    c = (mask >> 2) & 1
    e = (mask >> 4) & 1
    f = (mask >> 5) & 1
    r = (a + c + e + f) & 1
    if not b and not r:
        return 1
    if n % 2 == 0:
        return 0
    if not b:  # chi_4
        return 1 if n % 4 == 1 else -1
    if not r:  # chi_8
        return 1 if n % 8 in (1, 7) else -1
    # chi_8'
    return 1 if n % 8 in (1, 3) else -1


def atom_character(mask, n):
    value = two_primary_atom(mask, n)
    for bit, q in zip((2, 3, 4, 5, 6), ODD_ATOM_PRIMES):
        if (mask >> bit) & 1:
            value *= legendre(n, q)
    return value


def jacobi(a, odd_n):
    """Jacobi symbol (a/odd_n), for positive odd denominator."""
    require(odd_n > 0 and odd_n % 2 == 1,
            "Jacobi denominator must be positive odd")
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


def kronecker(D, n):
    """Kronecker (D/n) for D from the mask table and n >= 0."""
    require(n >= 0, "checker iterates nonnegative period representatives")
    if n == 0:
        # Treat this as the Dirichlet character on Z/nZ, including its value
        # at the zero residue: only the conductor-one character is nonzero.
        return 1 if D == 1 else 0
    sign = 1
    while n % 2 == 0:
        if D % 2 == 0:
            return 0
        if D % 8 in (3, 5):
            sign = -sign
        n //= 2
    return sign * jacobi(D, n)


def conrey_reference():
    """Load only the existing script's label routine and FLINT character API."""
    try:
        from flint import dirichlet_char
    except ImportError:
        return None, None, "python-flint is not installed"
    namespace = runpy.run_path(str(HERE / Path(REFERENCE_SCRIPT).name),
                               run_name="genus_full_direct_reference")
    return namespace["conrey_number"], dirichlet_char, None


def encoded_value(value):
    require(value in (-1, 0, 1), f"nonquadratic value {value}")
    return bytes((value + 1,))


def check_all(output_path, require_flint):
    input_hashes = verify_sources()
    conrey_fn, flint_character, flint_unavailable = conrey_reference()
    if require_flint:
        require(flint_unavailable is None, flint_unavailable or "FLINT unavailable")

    started = time.monotonic()
    rows = []
    total_period = 0
    checked_flint = 0
    for mask in range(128):
        D = discriminant(mask)
        conductor = abs(D)
        require(conductor >= 1, f"invalid conductor at mask={mask}")
        if conrey_fn is not None:
            label = conrey_fn(D)
            char = flint_character(conductor, label)
            require(char.conductor() == conductor,
                    f"FLINT conductor mismatch at mask={mask}")
            require(char.is_real() and char.order() <= 2,
                    f"FLINT character is not quadratic at mask={mask}")
        else:
            label = None
            char = None

        row_digest = sha256()
        flint_digest = sha256() if char is not None else None
        zeros = 0
        for n in range(conductor):
            atom = atom_character(mask, n)
            symbol = kronecker(D, n)
            require(atom == symbol,
                    f"atom/Kronecker mismatch: mask={mask}, D={D}, n={n}, "
                    f"atom={atom}, Kronecker={symbol}")
            row_digest.update(encoded_value(atom))
            if atom == 0:
                zeros += 1
            if char is not None:
                flint_value = char(n)
                require(flint_value == symbol,
                        f"atom/Conrey mismatch: mask={mask}, D={D}, label={label}, "
                        f"n={n}, atom={atom}, Conrey={flint_value}")
                # FLINT returns an acb value even for these exact real
                # characters. Equality with the integer establishes the
                # expected value; hash the checked integer, not the wrapper.
                flint_digest.update(encoded_value(symbol))
                checked_flint += 1
        rows.append({
            "mask": mask,
            "D": D,
            "conductor": conductor,
            "conrey_number_from_reference": label,
            "residue_classes_checked": conductor,
            "zero_values_checked": zeros,
            "atom_digest_sha256": row_digest.hexdigest(),
            "conrey_digest_sha256":
                flint_digest.hexdigest() if flint_digest is not None else None,
        })
        total_period += conductor

    require(total_period == EXPECTED_PERIOD_SUM,
            f"period sum changed: {total_period} != {EXPECTED_PERIOD_SUM}")
    require(sum(row["residue_classes_checked"] for row in rows) == total_period,
            "internal period count mismatch")
    result = {
        "status": "pass",
        "scope": (
            "Exact finite check of the explicit 2-primary times selected odd "
            "Legendre atom formula against an independent Kronecker routine "
            "for every residue in all 128 conductor periods. This is finite "
            "evidence, not the missing Lean theorem or analytic verification."
        ),
        "python": sys.version.split()[0],
        "input_source_sha256": input_hashes["verified"],
        "absent_lean_source_pins": input_hashes["absent_lean_sources"],
        "lean_source_pin_coverage": (
            "all pinned Lean sources verified" if not input_hashes["absent_lean_sources"]
            else "package-only mode: present Lean source pins verified; absent pins not re-verified"
        ),
        "checker_sha256": sha256_file(Path(__file__).resolve()),
        "masks_checked": len(rows),
        "residue_classes_checked": total_period,
        "conductor_sum_expected_from_Lean": EXPECTED_PERIOD_SUM,
        "zero_character_values_checked": sum(row["zero_values_checked"] for row in rows),
        "flint_conrey_check": {
            "status": "pass" if flint_character is not None else "unavailable",
            "reason": flint_unavailable,
            "coefficients_checked": checked_flint,
            "source": REFERENCE_SCRIPT,
        },
        "wall_seconds": round(time.monotonic() - started, 3),
        "rows": rows,
    }
    if flint_character is not None:
        import flint
        result["flint_conrey_check"]["python_flint_version"] = flint.__version__
        require(checked_flint == total_period,
                "not every residue was checked against FLINT")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"PASS {len(rows)} masks; {total_period} residue classes")
    if flint_character is not None:
        print(f"PASS {checked_flint} FLINT Conrey coefficients")
    else:
        print(f"FLINT Conrey comparison unavailable: {flint_unavailable}")
    print(f"result: {output_path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--require-flint", action="store_true",
                        help="fail if python-flint Conrey comparison is unavailable")
    args = parser.parse_args()
    check_all(args.output, args.require_flint)


if __name__ == "__main__":
    main()
