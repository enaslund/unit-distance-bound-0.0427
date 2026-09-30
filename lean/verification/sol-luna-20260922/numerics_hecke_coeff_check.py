#!/usr/bin/env python3
"""Recompute the first 128 coefficients of one H7 Hecke moment row.

The checker uses only the standard library. It evaluates the defining
quadratic-residue character data and local Euler factors directly; it does not
import or execute the manuscript moment producer or its arithmetic helpers.
"""

from __future__ import annotations

import hashlib
import json
from math import comb
from pathlib import Path


HERE = Path(__file__).resolve().parent
PACKAGE_ROOT = HERE.parents[1]
REPO_ROOT = HERE.parents[2]
MOMENTS = REPO_ROOT / "publication/nonabelian-dyadic-lower-bound/research/h7-pure-moments.json"
ARITHMETIC = REPO_ROOT / "publication/nonabelian-dyadic-lower-bound/research/h7-pure-arithmetic.json"
FIXTURE = HERE / "numerics_hecke_coeff_fixture.json"
MOMENTS_SHA256 = "c999ec7882f758e72f683fc3572406ed0d325ff674958e23a0349f322ecd84bf"
ARITHMETIC_SHA256 = "e1d892ba20f90bf6ea15e52f710ead0b8806a6db50d95792a76ebe2552183948"
FIXTURE_SHA256 = "db0e2050cf3e9a3d1f0b79f4481b55609b52fb071a2ade4c93acfc21e864a1ae"
BAD = (2, 3, 5, 7, 11, 13, 17)
MODULUS = 2_042_040
LIMIT = 128


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def jacobi(a: int, n: int) -> int:
    if n <= 0 or n % 2 == 0:
        raise ValueError("Jacobi denominator must be positive odd")
    a %= n
    sign = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            sign = -sign
        a %= n
    return sign if n == 1 else 0


def sqrt_mod_prime(a: int, p: int) -> int:
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        raise AssertionError(f"nonsquare radicand {a} modulo {p}")
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    c, r, t, m = pow(z, q, p), pow(a, (q + 1) // 2, p), pow(a, q, p), s
    while t != 1:
        i, t2 = 1, t * t % p
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
            if i >= m:
                raise AssertionError("Tonelli-Shanks failed")
        b = pow(c, 1 << (m - i - 1), p)
        r, c, t, m = r * b % p, b * b % p, t * b * b % p, i
    assert r * r % p == a
    return r


def vector_for_residue(r: int) -> int:
    """Eight quadratic-residue bits used by the defining class table."""
    if r % 2 == 0 or any(r % p == 0 for p in BAD):
        raise AssertionError("residue is not a unit modulo the bad primes")
    value = int(r % 4 == 3) | (int(r % 8 in (3, 5)) << 1)
    for i, p in enumerate(BAD[1:], start=1):
        symbol = jacobi(p, r)
        if symbol == 0:
            raise AssertionError("unexpected nonunit Jacobi symbol")
        if symbol < 0:
            value |= 1 << (i + 1)
    return value


def action_table(form: int) -> list[int]:
    actions = []
    for vector in range(256):
        radical = 0
        square = (form & vector).bit_count() & 1
        bit = 8
        for i in range(8):
            for j in range(i + 1, 8):
                if (form >> bit) & 1:
                    if (vector >> i) & 1:
                        radical ^= 1 << j
                    if (vector >> j) & 1:
                        radical ^= 1 << i
                    square ^= ((vector >> i) & 1) & ((vector >> j) & 1)
                bit += 1
        if radical:
            actions.append(-2 if square else 2)
        else:
            if square:
                raise AssertionError("form has a nontrivial square action with trivial radical")
            actions.append(0)
    return actions


def central_sign(p: int, base: list[int], eta: list[int]) -> int:
    u = sqrt_mod_prime(base[0], p)
    v = sqrt_mod_prime(base[1], p)
    signs = set()
    for uu in (u, -u):
        for vv in (v, -v):
            value = (eta[0] + eta[1] * uu + eta[2] * vv + eta[3] * uu * vv) % p
            symbol = pow(value, (p - 1) // 2, p)
            if symbol not in (1, p - 1):
                raise AssertionError(f"zero central character at p={p}")
            signs.add(1 if symbol == 1 else -1)
    if len(signs) != 1:
        raise AssertionError(f"central character varies among embeddings at p={p}: {signs}")
    return signs.pop()


def inverse_series(denominator: list[int], exponent: int) -> list[int]:
    coeff = [0] * (exponent + 1)
    coeff[0] = 1
    for n in range(1, exponent + 1):
        coeff[n] = -sum(denominator[j] * coeff[n - j]
                       for j in range(1, min(n, len(denominator) - 1) + 1))
    return coeff


def local_coefficients(p: int, row: dict[str, object], form_actions: list[int], base: list[int], eta: list[int]) -> list[int]:
    max_exp = 0
    power = p
    while power <= LIMIT:
        max_exp += 1
        power *= p
    bad = row["bad_euler_denominators"]
    if str(p) in bad:
        pair_coeffs = bad[str(p)]
        if any(imag for _, imag in pair_coeffs):
            raise AssertionError("selected row unexpectedly has nonreal bad factor")
        return inverse_series([int(re) for re, _ in pair_coeffs], max_exp)

    residue = p % MODULUS
    vector = vector_for_residue(residue)
    code = form_actions[vector]
    if code == 0:
        code = central_sign(p, base, eta)
    # Twist by the row's quadratic character, whose square-class mask is the
    # positive-prime factorization of |twist| with bit 0 for negative sign.
    twist = int(row["twist"])
    twist_mask = int(twist < 0)
    n = abs(twist)
    for i, bad_p in enumerate(BAD, start=1):
        if n % bad_p == 0:
            n //= bad_p
            twist_mask |= 1 << i
    if n != 1:
        raise AssertionError("twist has support outside the declared bad primes")
    if code in (-1, 1) and (twist_mask & vector).bit_count() % 2:
        code = -code

    coeff = [0] * (max_exp + 1)
    coeff[0] = 1
    for k in range(1, max_exp + 1):
        if code in (-2, 2):
            if k % 2 == 0:
                j = k // 2
                coeff[k] = (j + 1) * (-1 if code < 0 and j % 2 else 1)
        elif code in (-1, 1):
            coeff[k] = comb(k + 3, 3) * (code**k)
        else:
            raise AssertionError(f"invalid local action code {code}")
    return coeff


def first128(row: dict[str, object], sector: dict[str, object]) -> list[list[int]]:
    form_actions = action_table(int(sector["form_hex"], 16))
    base = list(map(int, sector["base_radicands"]))
    eta = list(map(int, sector["eta_coefficients"]))
    least = list(range(LIMIT + 1))
    for p in range(2, LIMIT + 1):
        if least[p] == p:
            for n in range(p, LIMIT + 1, p):
                if least[n] == n:
                    least[n] = p
    local = {p: local_coefficients(p, row, form_actions, base, eta)
             for p in range(2, LIMIT + 1) if least[p] == p}
    out = [(0, 0)] * (LIMIT + 1)
    out[1] = (1, 0)
    for n in range(2, LIMIT + 1):
        p = least[n]
        q, k = n, 0
        while q % p == 0:
            q //= p
            k += 1
        value = local[p][k]
        re, im = out[q]
        out[n] = (re * value, im * value)
    return [[re, im] for re, im in out[1:]]


def selected_inputs() -> tuple[dict[str, object], dict[str, object], bool]:
    """Prefer the compact fixture; bind it back to full tables when present."""
    if FIXTURE.is_file():
        fixture_hash = digest(FIXTURE)
        if fixture_hash != FIXTURE_SHA256:
            raise AssertionError(f"fixture hash mismatch: {fixture_hash}")
        fixture = json.loads(FIXTURE.read_text())
        if fixture.get("schema") != "unit-distance-h7-hecke-prefix-fixture-v1":
            raise AssertionError("unexpected Hecke fixture schema")
        sources = fixture.get("source_sha256", {})
        if sources != {
            "h7-pure-moments.json": MOMENTS_SHA256,
            "h7-pure-arithmetic.json": ARITHMETIC_SHA256,
        }:
            raise AssertionError("fixture source bindings changed")
        # A source checkout has the original full tables; a standalone package
        # carries just the bounded fixture and its pinned source provenance.
        if MOMENTS.exists() and digest(MOMENTS) != MOMENTS_SHA256:
            raise AssertionError("available full moment table does not match fixture binding")
        if ARITHMETIC.exists() and digest(ARITHMETIC) != ARITHMETIC_SHA256:
            raise AssertionError("available full arithmetic table does not match fixture binding")
        if MOMENTS.exists() and ARITHMETIC.exists():
            moment_data = json.loads(MOMENTS.read_text())
            arithmetic_data = json.loads(ARITHMETIC.read_text())
            source_sector = next(s for s in arithmetic_data["sectors"] if s["mask"] == moment_data["mask"])
            source_row = next(r for r in moment_data["rows"] if r["twist"] == -1)
            for key, value in fixture["sector"].items():
                if source_sector.get(key) != value:
                    raise AssertionError(f"pure H7 fixture sector field {key} differs from source")
            for key, value in fixture["row"].items():
                if source_row.get(key) != value:
                    raise AssertionError(f"pure H7 fixture row field {key} differs from source")
        return fixture["row"], fixture["sector"], True

    if not MOMENTS.is_file() or not ARITHMETIC.is_file():
        raise FileNotFoundError("need the compact fixture or both full research source tables")
    for path, expected in ((MOMENTS, MOMENTS_SHA256), (ARITHMETIC, ARITHMETIC_SHA256)):
        actual = digest(path)
        if actual != expected:
            raise AssertionError(f"input hash mismatch for {path.name}: {actual}")
    moment_data = json.loads(MOMENTS.read_text())
    arithmetic_data = json.loads(ARITHMETIC.read_text())
    sector = next(s for s in arithmetic_data["sectors"] if s["mask"] == moment_data["mask"])
    row = next(r for r in moment_data["rows"] if r["twist"] == -1)
    return row, sector, False


def main() -> None:
    if not __debug__:
        raise RuntimeError("Python assertions are required for this checker")
    row, sector, used_fixture = selected_inputs()
    expected = row["first128_complex_coefficients"]
    computed = first128(row, sector)
    if computed != expected:
        for n, (a, b) in enumerate(zip(computed, expected), start=1):
            if a != b:
                raise AssertionError(f"first mismatch at n={n}: recomputed {a}, recorded {b}")
        raise AssertionError("coefficient sequence length mismatch")
    print("PASS independent H7 Hecke coefficient prefix")
    print(f"moment_table_sha256={MOMENTS_SHA256}")
    print(f"arithmetic_source_sha256={ARITHMETIC_SHA256}")
    if used_fixture:
        print(f"fixture_sha256={FIXTURE_SHA256}")
        print(f"package_root={PACKAGE_ROOT}")
    print(f"sector=1920; twist=-1; conductor={row['conductor']}; coefficients=128")
    print("comparison=all 128 complex coefficients matched exactly")
    check_additional_families()


# Additional family rows use distinct local ranks and are derived below from
# residue characters and the defining local Euler factors.
FAMILY_FIXTURE = HERE / "numerics_hecke_family_fixture.json"
FAMILY_FIXTURE_SHA256 = "5fd9c83deb0fcdef56d314657ae8e1c7408c5508e652834e32cdabc3de234200"
FAMILY_SOURCE_HASHES = {
    "h6-low-degree-arithmetic.json": "b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771",
    "h6-low-degree-moments-1586.json": "a7e65537a05389f11115a8cf64c186ead6b1dc4973a8c5f862f31a34fdeb40f1",
    "h7-low-arithmetic.json": "4453a7fe7549ec3e189817e9081bb24c1d3244c3b1249604ab811ab289bf554f",
    "h7-low-moments-274.json": "0777fc81c8a9a6bcff795371e3f7f42095d86e268f141c0dba72777b40e82227",
    "h7-octic-arithmetic.json": "2c8d752f6206b6793b37d91ca9ad343b6c3c4ff92f61fed9ade9e307f0013836",
    "h7-octic-moments-307.json": "1249e9d714685fb0b92ce09c78578248b5d7a1d2a4dfab68252056ed7887063d",
}


def generic_central_sign(p: int, base: list[int], eta: list[int]) -> int:
    roots = [sqrt_mod_prime(a, p) for a in base]
    signs = set()
    for mask in range(1 << len(roots)):
        value = 0
        for term, coefficient in enumerate(eta):
            monomial = int(coefficient)
            for i, root in enumerate(roots):
                if term >> i & 1:
                    monomial *= -root if mask >> i & 1 else root
            value += monomial
        symbol = pow(value % p, (p - 1) // 2, p)
        if symbol not in (1, p - 1):
            raise AssertionError(f"zero central character at p={p}")
        signs.add(1 if symbol == 1 else -1)
    if len(signs) != 1:
        raise AssertionError(f"central character varies among embeddings at p={p}: {signs}")
    return signs.pop()


def rank4_local_denominator(code: int, twist_sign: int) -> list[int]:
    if code in (-2, 2):
        return [1, 0, -code, 0, 1]
    sign = code * twist_sign
    return [comb(4, j) * (-sign) ** j for j in range(5)]


def rank8_local_denominator(code: int, twist_sign: int) -> list[int]:
    if code in (-2, 2):
        return [comb(4, j // 2) * (-code // 2) ** (j // 2) if j % 2 == 0 else 0
                for j in range(9)]
    sign = code * twist_sign
    return [comb(8, j) * (-sign) ** j for j in range(9)]


def real_bad_denominator(row: dict[str, object], p: int) -> list[int]:
    result = []
    for re, im in row["bad_euler_denominators"][str(p)]:
        if int(im) != 0:
            raise AssertionError(f"selected bad Euler factor at p={p} is nonreal")
        result.append(int(re))
    return result


def rank2_first(row: dict[str, object], sector: dict[str, object], limit: int) -> list[list[int]]:
    """Degree-two Euler factors from two quadratic residue characters."""
    a, b = int(sector["base_radicands"][0]), int(sector["norm_squareclass"])
    x, y = map(int, sector["eta_coefficients"][:2])
    twist = int(row["twist"])
    least = list(range(limit + 1))
    for p in range(2, limit + 1):
        if least[p] == p:
            for n in range(p, limit + 1, p):
                if least[n] == n:
                    least[n] = p
    local: dict[int, list[int]] = {}
    bad = row["bad_euler_denominators"]
    for p in range(2, limit + 1):
        if least[p] != p:
            continue
        if str(p) in bad:
            local[p] = real_bad_denominator(row, p)
            continue
        sa = pow(a % p, (p - 1) // 2, p)
        sb = pow(b % p, (p - 1) // 2, p)
        sa = 0 if a % p == 0 else (1 if sa == 1 else -1)
        sb = 0 if b % p == 0 else (1 if sb == 1 else -1)
        if sa == sb == 1:
            root = sqrt_mod_prime(a, p)
            eps = pow((x + y * root) % p, (p - 1) // 2, p)
            conjugate = pow((x - y * root) % p, (p - 1) // 2, p)
            if eps not in (1, p - 1) or conjugate != eps:
                raise AssertionError(f"quadratic trace is not rational at p={p}")
            trace, determinant = 2 * (1 if eps == 1 else -1), 1
        else:
            trace, determinant = 0, sa * sb
        twist_sign = 1 if pow(twist % p, (p - 1) // 2, p) == 1 else -1
        trace *= twist_sign
        local[p] = [1, -trace, determinant]
    coefficients = [(0, 0)] * (limit + 1)
    coefficients[1] = (1, 0)
    for n in range(2, limit + 1):
        p = least[n]
        m = n
        re = im = 0
        for j in (1, 2):
            if m % p:
                break
            m //= p
            c = local[p][j]
            re -= c * coefficients[m][0]
            im -= c * coefficients[m][1]
        coefficients[n] = (re, im)
    return [[r, i] for r, i in coefficients[1:]]


def higher_rank_prefix(row: dict[str, object], sector: dict[str, object], limit: int) -> list[list[int]]:
    """Degree-four/eight good factors from genus Frobenius and eta residues."""
    form = int(sector["form_hex"], 16)
    actions = action_table(form)
    base = list(map(int, sector["base_radicands"]))
    eta = list(map(int, sector["eta_coefficients"]))
    rank = int(sector["dimension"])
    twist = int(row["twist"])
    least = list(range(limit + 1))
    for p in range(2, limit + 1):
        if least[p] == p:
            for n in range(p, limit + 1, p):
                if least[n] == n:
                    least[n] = p
    local: dict[int, list[int]] = {}
    bad = row["bad_euler_denominators"]
    for p in range(2, limit + 1):
        if least[p] != p:
            continue
        if str(p) in bad:
            local[p] = real_bad_denominator(row, p)
            continue
        vector = vector_for_residue(p % MODULUS)
        code = actions[vector]
        if code == 0:
            code = generic_central_sign(p, base, eta)
        twist_sign = 1 if pow(twist % p, (p - 1) // 2, p) == 1 else -1
        if rank == 4:
            local[p] = rank4_local_denominator(code, twist_sign)
        elif rank == 8:
            local[p] = rank8_local_denominator(code, twist_sign)
        else:
            raise AssertionError(f"unsupported higher rank {rank}")
    out = [(0, 0)] * (limit + 1)
    out[1] = (1, 0)
    for n in range(2, limit + 1):
        p = least[n]
        m = n
        re = im = 0
        for j in range(1, rank + 1):
            if m % p:
                break
            m //= p
            cr = local[p][j]
            vr, vi = out[m]
            re -= cr * vr
            im -= cr * vi
        out[n] = (re, im)
    return [[r, i] for r, i in out[1:]]


def check_additional_families() -> None:
    if digest(FAMILY_FIXTURE) != FAMILY_FIXTURE_SHA256:
        raise AssertionError("Hecke family fixture hash mismatch")
    fixture = json.loads(FAMILY_FIXTURE.read_text())
    if fixture.get("schema") != "unit-distance-hecke-family-fixture-v1":
        raise AssertionError("unexpected family fixture schema")
    if fixture.get("source_sha256") != FAMILY_SOURCE_HASHES:
        raise AssertionError("family fixture source hashes changed")
    available_sources = {}
    for name, expected_hash in FAMILY_SOURCE_HASHES.items():
        full = REPO_ROOT / "publication/nonabelian-dyadic-lower-bound/research" / name
        if full.exists() and digest(full) != expected_hash:
            raise AssertionError(f"available family source hash mismatch: {name}")
        if full.exists():
            available_sources[name] = json.loads(full.read_text())
    families = fixture["families"]
    if set(families) != {"mixed_quadratic", "mixed_quartic", "mixed_octic"}:
        raise AssertionError("unexpected selected family labels")
    outputs = []
    for label, expected_rank in (("mixed_quadratic", 2), ("mixed_quartic", 4), ("mixed_octic", 8)):
        record = families[label]
        row, sector = record["row"], record["sector"]
        if int(sector["dimension"]) != expected_rank or row["twist"] != -1:
            raise AssertionError(f"wrong representative label for {label}")
        if record["arithmetic_source"] in available_sources:
            source = available_sources[record["arithmetic_source"]]
            if "sectors" in source:
                source_sector = next(s for s in source["sectors"] if s["mask"] == sector["mask"])
            else:
                source_sector = source
            for key, value in sector.items():
                if source_sector.get(key) != value:
                    raise AssertionError(f"{label}: fixture arithmetic field {key} differs from source")
        if record["moments_source"] in available_sources:
            source = available_sources[record["moments_source"]]
            source_row = next(r for r in source["rows"] if r["twist"] == row["twist"])
            for key, value in row.items():
                if source_row.get(key) != value:
                    raise AssertionError(f"{label}: fixture moment field {key} differs from source")
        if expected_rank == 2:
            # This source table records a complete-vector hash at N=981.
            limit = int(row["N"])
            computed = rank2_first(row, sector, limit)
            as_tuples = [tuple(v) for v in [[0, 0], *computed]]
            actual_hash = hashlib.sha256(json.dumps(as_tuples).encode()).hexdigest()
            if actual_hash != row["signed_coefficients_sha256"]:
                raise AssertionError(f"{label}: complete signed coefficient hash mismatch")
            checked = limit
            compare = "complete coefficient vector hash"
        else:
            computed = higher_rank_prefix(row, sector, LIMIT)
            expected = row["first128_complex_coefficients"]
            if computed != expected:
                for n, (got, target) in enumerate(zip(computed, expected), start=1):
                    if got != target:
                        raise AssertionError(f"{label}: first mismatch at n={n}: {got} vs {target}")
                raise AssertionError(f"{label}: prefix length mismatch")
            checked = LIMIT
            compare = "exact recorded first128 list"
        outputs.append(f"{label}=mask{sector['mask']},rank{expected_rank},twist-1,n=1..{checked} ({compare})")
    source_status = "full source rows checked" if len(available_sources) == len(FAMILY_SOURCE_HASHES) else "compact hash-pinned fixture"
    print(f"PASS independent Hecke family rows ({source_status}): " + "; ".join(outputs))


if __name__ == "__main__":
    main()
