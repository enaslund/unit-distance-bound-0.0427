#!/usr/bin/env python3
"""Independent finite-prefix audit of every new H7 quartic/octic Euler row.

For each row this derives coefficients n<=128 from the literal norm form,
Frobenius form, quadratic twist, bad Euler denominators, and any quartic phase.
It does not read the stored coefficient vector until the final comparison.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
from math import comb
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RESEARCH = ROOT / "publication/nonabelian-dyadic-lower-bound/research"
FIXTURE = HERE / "h7_all_new_coefficients_fixture.json"
OUT = HERE / "h7_all_new_coefficients_check.json"
HELPER = HERE / "numerics_hecke_coeff_check.py"
LIMIT = 128
FIXTURE_SHA256 = "a28de6177ddb0ce6513c3520cbc2c342fcb109ab94868a1775aafe7c9fe933be"

PINNED = {
    "h7-euler.json": "4f01e9ae1f0f79f6575955745c1bdf6ce349a03b6990e2e4189a5205426088af",
    "h7-low-euler-12000.json": "e18811d9a91281e1fc3fcc81d49130ad5968ba5611e6e649d7061addea32525e",
    "h7-pure-euler-12000.json": "441ecbc24ae113807de6de5b2e911c356c98c6df6947bdac7e94233cb49a2d3e",
    "h7-octic-euler-12000.json": "e049579a82034602de22d4d3517817a2f824889155e9ec90613e5de906207151",
    "h7-low-arithmetic.json": "4453a7fe7549ec3e189817e9081bb24c1d3244c3b1249604ab811ab289bf554f",
    "h7-pure-arithmetic.json": "e1d892ba20f90bf6ea15e52f710ead0b8806a6db50d95792a76ebe2552183948",
    "h7-octic-arithmetic.json": "2c8d752f6206b6793b37d91ca9ad343b6c3c4ff92f61fed9ade9e307f0013836",
    "numerics_hecke_coeff_check.py": "3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329",
}


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def load_helper():
    expected = PINNED["numerics_hecke_coeff_check.py"]
    actual = sha(HELPER)
    if actual != expected:
        raise ValueError(f"pinned arithmetic-helper hash mismatch: {actual}")
    spec = importlib.util.spec_from_file_location("h7_coeff_reference", HELPER)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load the pinned small-prime arithmetic helper")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def research_inputs() -> tuple[list[dict[str, object]], dict[str, str]]:
    for name, expected in PINNED.items():
        path = HELPER if name == "numerics_hecke_coeff_check.py" else RESEARCH / name
        actual = sha(path)
        if actual != expected:
            raise ValueError(f"pinned source hash mismatch for {name}: {actual}")

    top = json.loads((RESEARCH / "h7-euler.json").read_text())
    for name in ("h7-low-euler-12000.json", "h7-pure-euler-12000.json", "h7-octic-euler-12000.json"):
        if top["source_sha256"].get(f"nonabelian-dyadic-lower-bound/research/{name}") != PINNED[name]:
            raise ValueError(f"top H7 Euler receipt does not bind {name}")

    low_agg = json.loads((RESEARCH / "h7-low-euler-12000.json").read_text())
    pure_agg = json.loads((RESEARCH / "h7-pure-euler-12000.json").read_text())
    octic_agg = json.loads((RESEARCH / "h7-octic-euler-12000.json").read_text())
    low_arith = json.loads((RESEARCH / "h7-low-arithmetic.json").read_text())
    pure_arith = json.loads((RESEARCH / "h7-pure-arithmetic.json").read_text())
    octic_arith = json.loads((RESEARCH / "h7-octic-arithmetic.json").read_text())
    arithmetic_by_family = {
        "mixed_quartic": {s["mask"]: s for s in low_arith["sectors"]},
        "pure_quartic": {s["mask"]: s for s in pure_arith["sectors"]},
        "octic": {s["mask"]: s for s in octic_arith["sectors"]},
    }
    sources: dict[str, str] = {name: sha(RESEARCH / name) for name in PINNED if name != "numerics_hecke_coeff_check.py"}
    records = []

    for family, prefix, aggregate, arith in (
        ("mixed_quartic", "h7-low-moments-", low_agg, arithmetic_by_family["mixed_quartic"]),
        ("pure_quartic", "h7-pure-moments", pure_agg, arithmetic_by_family["pure_quartic"]),
        ("octic", "h7-octic-moments-", octic_agg, arithmetic_by_family["octic"]),
    ):
        if family == "pure_quartic":
            files = [RESEARCH / "h7-pure-moments.json"]
        else:
            files = sorted(RESEARCH.glob(prefix + "*.json"))
        manifest = aggregate["source_sha256"]
        for path in files:
            digest = sha(path)
            source_names = [k for k, v in manifest.items()
                            if (Path(k).name == path.name and v == digest)]
            if len(source_names) != 1:
                raise ValueError(f"{path.name} is not uniquely hash-bound by its Euler receipt")
            sources[path.name] = digest
            moment = json.loads(path.read_text())
            mask = int(moment["mask"])
            sector = arith.get(mask)
            if sector is None:
                raise ValueError(f"no arithmetic sector for {family} mask {mask}")
            if family == "pure_quartic":
                row_list = moment["rows"]
            else:
                row_list = moment["rows"]
            # The arithmetic record supplies the literal row description; the
            # moment file's prefix is retained solely as the expected value.
            arith_rows = {int(r["twist"]): r for r in sector["rows"]}
            if len(arith_rows) != len(sector["rows"]):
                raise ValueError(f"duplicate twists in arithmetic sector {mask}")
            if len(row_list) != len(arith_rows):
                raise ValueError(f"row count differs for {family} mask {mask}")
            for moment_row in row_list:
                twist = int(moment_row["twist"])
                arithmetic_row = arith_rows.get(twist)
                if arithmetic_row is None:
                    raise ValueError(f"missing arithmetic row {family} mask {mask}, twist {twist}")
                for key, value in arithmetic_row.items():
                    if moment_row.get(key) != value:
                        raise ValueError(f"copied row field differs: {family} mask={mask} twist={twist} key={key}")
                records.append({
                    "family": family,
                    "mask": mask,
                    "twist": twist,
                    "sector": {
                        "mask": int(sector["mask"]),
                        "dimension": int(sector["dimension"]),
                        "form_hex": sector["form_hex"],
                        "base_radicands": sector["base_radicands"],
                        "eta_coefficients": sector["eta_coefficients"],
                        "dirichlet_twist_modulus": sector.get("dirichlet_twist_modulus"),
                    },
                    "row": {
                        key: arithmetic_row[key]
                        for key in ("twist", "bad_euler_denominators", "quartic_exponent",
                                    "quartic_modulus", "factor_multiplicity")
                        if key in arithmetic_row
                    },
                    "expected_first128": moment_row["first128_complex_coefficients"],
                    "factor_multiplicity": int(arithmetic_row["factor_multiplicity"]),
                    "moment_file": path.name,
                })
    return records, sources


def make_fixture() -> None:
    records, sources = research_inputs()
    fixture = {
        "schema": "h7-new-analytic-row-prefix-fixture-v1",
        "source_sha256": sources,
        "records": records,
    }
    FIXTURE.write_text(json.dumps(fixture, separators=(",", ":")) + "\n")
    print(f"fixture rows={len(records)} sha256={sha(FIXTURE)} bytes={FIXTURE.stat().st_size}")


def fixture_inputs() -> tuple[list[dict[str, object]], dict[str, str]]:
    if not FIXTURE.is_file():
        raise FileNotFoundError("missing full-row fixture")
    actual = sha(FIXTURE)
    if actual != FIXTURE_SHA256:
        raise ValueError(f"pinned full-row fixture hash mismatch: {actual}")
    fixture = json.loads(FIXTURE.read_text())
    if fixture.get("schema") != "h7-new-analytic-row-prefix-fixture-v1":
        raise ValueError("unexpected fixture schema")
    return fixture["records"], fixture["source_sha256"]


def mul(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def add(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (a[0] + b[0], a[1] + b[1])


def cscale(a: tuple[int, int], k: int) -> tuple[int, int]:
    return (a[0] * k, a[1] * k)


def cpow(a: tuple[int, int], n: int) -> tuple[int, int]:
    out = (1, 0)
    for _ in range(n):
        out = mul(out, a)
    return out


def phase_at(p: int, row: dict[str, object], sector: dict[str, object]) -> tuple[int, int]:
    exponent = int(row.get("quartic_exponent", 0))
    modulus = row.get("quartic_modulus") or sector.get("dirichlet_twist_modulus") or 1
    if not exponent:
        return (1, 0)
    modulus = int(modulus)
    if modulus == 5:
        table = {1: (1, 0), 2: (0, 1), 3: (0, -1), 4: (-1, 0)}
    elif modulus == 13:
        table = {}
        value, powers = 1, ((1, 0), (0, 1), (-1, 0), (0, -1))
        for j in range(12):
            table[value] = powers[j % 4]
            value = value * 2 % 13
    else:
        raise ValueError(f"unsupported quartic character modulus {modulus}")
    if p % modulus not in table:
        raise ValueError(f"quartic phase undefined at good prime {p}")
    return table[p % modulus]


def least_prime_factors(nmax: int) -> list[int]:
    spf = list(range(nmax + 1))
    for p in range(2, int(nmax**0.5) + 1):
        if spf[p] == p:
            for n in range(p * p, nmax + 1, p):
                if spf[n] == n:
                    spf[n] = p
    return spf


def inverse_coefficients(den: list[tuple[int, int]], kmax: int) -> list[tuple[int, int]]:
    coeff = [(0, 0)] * (kmax + 1)
    coeff[0] = (1, 0)
    for k in range(1, kmax + 1):
        value = (0, 0)
        for j in range(1, min(k, len(den) - 1) + 1):
            value = add(value, mul(den[j], coeff[k - j]))
        coeff[k] = (-value[0], -value[1])
    return coeff


def recompute(row: dict[str, object], sector: dict[str, object], helper) -> list[list[int]]:
    rank = int(sector["dimension"])
    if rank not in (4, 8):
        raise ValueError(f"unexpected rank {rank}")
    actions = helper.action_table(int(sector["form_hex"], 16))
    bad = row["bad_euler_denominators"]
    local: dict[int, list[tuple[int, int]]] = {}
    spf = least_prime_factors(LIMIT)
    for p in range(2, LIMIT + 1):
        if spf[p] != p:
            continue
        kmax = 0
        q = p
        while q <= LIMIT:
            kmax += 1
            q *= p
        if str(p) in bad:
            den = [tuple(map(int, pair)) for pair in bad[str(p)]]
            local[p] = inverse_coefficients(den, kmax)
            continue
        vector = helper.vector_for_residue(p % helper.MODULUS)
        code = actions[vector]
        if code == 0:
            code = helper.generic_central_sign(
                p, list(map(int, sector["base_radicands"])),
                list(map(int, sector["eta_coefficients"])),
            )
        twist = int(row["twist"])
        twist_symbol = pow(twist % p, (p - 1) // 2, p)
        if twist_symbol not in (1, p - 1):
            raise ValueError(f"quadratic twist is ramified at undeclared good prime {p}")
        twist_sign = 1 if twist_symbol == 1 else -1
        if rank == 4:
            real = helper.rank4_local_denominator(code, twist_sign)
        else:
            real = helper.rank8_local_denominator(code, twist_sign)
        phase = phase_at(p, row, sector)
        exponent = int(row.get("quartic_exponent", 0))
        den = [mul((int(x), 0), cpow(phase, exponent * j)) for j, x in enumerate(real)]
        local[p] = inverse_coefficients(den, kmax)

    values = [(0, 0)] * (LIMIT + 1)
    values[1] = (1, 0)
    for n in range(2, LIMIT + 1):
        p = spf[n]
        q, k = n, 0
        while q % p == 0:
            q //= p
            k += 1
        values[n] = mul(values[q], local[p][k])
    return [list(v) for v in values[1:]]


def run(records: list[dict[str, object]], source_hashes: dict[str, str]) -> dict[str, object]:
    helper = load_helper()
    family_rows = {"mixed_quartic": 0, "pure_quartic": 0, "octic": 0}
    family_multiplicities = {key: 0 for key in family_rows}
    checked = 0
    for record in records:
        got = recompute(record["row"], record["sector"], helper)
        expected = record["expected_first128"]
        if got != expected:
            mismatch = next((i + 1 for i, (a, b) in enumerate(zip(got, expected)) if a != b), None)
            raise ValueError(
                f"coefficient mismatch family={record['family']} mask={record['mask']} "
                f"twist={record['twist']} n={mismatch} got={None if mismatch is None else got[mismatch-1]} "
                f"expected={None if mismatch is None else expected[mismatch-1]}"
            )
        family_rows[record["family"]] += 1
        family_multiplicities[record["family"]] += int(record["factor_multiplicity"])
        checked += LIMIT
    if family_rows != {"mixed_quartic": 136, "pure_quartic": 8, "octic": 78}:
        raise ValueError(f"unexpected row census {family_rows}")
    if family_multiplicities != {"mixed_quartic": 168, "pure_quartic": 8, "octic": 84}:
        raise ValueError(f"unexpected factor multiplicities {family_multiplicities}")
    return {
        "status": "PASS independent H7 new-row coefficient-prefix audit",
        "scope": "All new mixed-quartic, pure-quartic, and octic rows; first 128 coefficients per row, derived from literal arithmetic inputs and compared to stored moment prefixes.",
        "rows_checked": len(records),
        "coefficients_checked": checked,
        "factor_multiplicities_by_family": family_multiplicities,
        "analytic_rows_by_family": family_rows,
        "source_sha256": source_hashes,
        "checker_sha256": sha(Path(__file__)),
        "arithmetic_helper_sha256": sha(HELPER),
        "fixture_sha256": sha(FIXTURE),
        "fixture_bytes": FIXTURE.stat().st_size,
        "quartic_phase_rows": sum(bool(r["row"].get("quartic_exponent", 0)) for r in records),
        "quartic_phase_moduli": sorted({int(r["row"].get("quartic_modulus") or r["sector"].get("dirichlet_twist_modulus"))
                                         for r in records if r["row"].get("quartic_exponent", 0)}),
        "bad_prime_local_factors_used_from_literal_rows": True,
        "stored_coefficient_vectors_used_only_as_expected_values": True,
    }


def main() -> None:
    if not __debug__:
        raise RuntimeError("assertions are required; do not run Python with -O")
    if "--make-fixture" in __import__("sys").argv[1:]:
        make_fixture()
        return
    records, sources = fixture_inputs()
    result = run(records, sources)
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
