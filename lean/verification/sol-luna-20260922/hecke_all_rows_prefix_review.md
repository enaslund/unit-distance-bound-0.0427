# Independent H7 new-factor coefficient-prefix audit

## Result and scope

`hecke_all_rows_prefix_check.py` completed a guarded run successfully (exit 0, 0.92 seconds after admission with 19.2 GiB available). It recomputed and exactly matched all 28,416 complex-integer coefficients (a_n), (1\le n\le128), in the 222 new analytic rows:

| Family | Stored rows | Factor multiplicity |
|---|---:|---:|
| Mixed quartic | 136 | 168 |
| Pure quartic | 8 | 8 |
| Octic | 78 | 84 |
| **Total** | **222** | **260** |

It exercised 38 rows with a nontrivial quartic phase, at moduli 5 and 13. In the H7 analytic assembly, these 260 new factors supplement 576 inherited H6 factors, giving the 836-factor inventory. This check covers the 260 new-factor multiplicity only; it does not recompute the 576 inherited rows.

The compact fixture `h7_all_new_coefficients_fixture.json` is 339,343 bytes and is pinned in the checker by SHA-256 `a28de6177ddb0ce6513c3520cbc2c342fcb109ab94868a1775aafe7c9fe933be`. The coefficient replay receipt is `h7_all_new_coefficients_check.json`; the full-source fixture-generation receipt is `hecke_all_rows_prefix_fixture_generation.json`.

## Independent reconstruction

For every row, the checker takes the literal sector form, base radicands, eta coefficients, rank, row twist, quartic phase, factor multiplicity, and seven bad-prime denominator polynomials from the arithmetic tables. At each good prime through 128 it computes the genus Frobenius vector, evaluates the form action, and uses the eta norm-form residue when the form action is zero. It constructs the rank-four or rank-eight local denominator, multiplies its coefficients by the appropriate quartic phase when present, inverts that denominator as an exact Gaussian-integer power series, and combines the prime-power coefficients multiplicatively. At bad primes it uses the literal row denominator. Only after reconstruction does it compare with the stored `first128_complex_coefficients` vector.

The arithmetic routines for finite Frobenius vectors and form actions are from the separate, pinned helper `numerics_hecke_coeff_check.py` (SHA-256 `3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329`). `load_helper()` now checks this digest before import on every run, including fixture-only archive replay. That helper had previously been used on four representative rows; this checker extends the same independently written local-character method across every H7 new row and explicitly handles the nontrivial mod-5 and mod-13 phases. It does not execute the original moment producer or use its coefficient-generation routine.

Full-source validation occurs when running `hecke_all_rows_prefix_check.py --make-fixture`. That mode verifies the canonical H7 Euler receipt, the three group receipts, the three arithmetic tables, the helper, and each per-sector moment file before rebuilding the compact fixture. The top H7 receipt binds the group receipts; each group receipt hash binds its list of per-sector files. The generated fixture carries 67 per-family arithmetic/moment table hashes (3 arithmetic tables and 64 moment tables), plus 4 Euler receipt hashes, 71 hashes total. The helper source hash is separately pinned in the checker. The final guarded regeneration passed with exit 0, admission at 19.1 GiB, and stdout confirming 222 rows, the pinned fixture hash, and 339,343 bytes.

The compact fixture contains only the arithmetic row fields needed for reconstruction, expected coefficient prefixes, family labels, and source hashes, so the arithmetic comparison can be replayed without the large moment tables. **Ordinary checker execution only validates and reads the pinned compact fixture; it does not rehash the full research tables.** A simulated standalone layout containing only the checker, fixture, and pinned helper passed under the shared guard (exit 0, 0.92 seconds, 16.9 GiB available at admission). Its result is recorded in `hecke_all_rows_prefix_package_smoke.json`. After adding the unconditional helper digest check, full-source fixture regeneration, research replay, and this standalone replay all passed again; the fixture remained byte-identical.

## Limits

This is a finite-prefix check of the supplied arithmetic rows. It does not prove the global Artin-factor identification, the correctness of the original sector-to-field construction, the functional equations, the AFE estimates, the later moment bins, or the final H bound. The bad-prime local polynomials and norm-form data are trusted literal inputs whose provenance is hash-pinned, not independently derived here. The multiplicity total confirms the stated row-to-factor accounting for the new sectors, not the inherited 576-factor analytic computation.
