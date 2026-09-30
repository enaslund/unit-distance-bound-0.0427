# H6 mask-1586 plus-quartic coefficient replay

## Result

**PASS, finite scope:** the exact integer Dirichlet coefficients
`a_1,...,a_3922` reconstructed from PARI/GP maximal-order prime
decompositions for

* `K = Q[x]/(x^4 - 34x^2 + 429)`, and
* `B = Q[x]/(x^2 + 35)`,

agree entry-for-entry with the pinned H6 mask-1586, twist-`+1` quadratic
recurrence. Both serialized vector hashes are
`b9317cb66d83f606dbbeeecd2ad40f4e805afbfbda7bd04383b28b7e7f1e3489`;
there are zero mismatches among all 3922 entries. PARI/GP returned
maximal-order decomposition data for all 543 rational primes at most 3922.
The `nfcertify` checks for both fields returned empty vectors, which the
checker required before using any `idealprimedec` result. For hash
serialization, each coefficient array includes an unused zero at index 0;
the equality claim concerns exactly indices 1 through 3922.

The seven exact bad-local-factor comparisons all pass the polynomial
identity `D_K(T)=E_p(T) D_B(T)`, equivalently
`ζ_K,p/ζ_B,p = 1/E_p(T)`:

| `p` | residue degrees in `K` | residue degrees in `B` | row denominator `E_p(T)` |
|---:|---|---|---|
| 2 | `[2]` | `[2]` | `1` |
| 3 | `[1,1,1]` | `[1,1]` | `1−T` |
| 5 | `[2]` | `[1]` | `1+T` |
| 7 | `[2]` | `[1]` | `1+T` |
| 11 | `[1,1,1]` | `[1,1]` | `1−T` |
| 13 | `[1,2]` | `[1,1]` | `1+T` |
| 17 | `[1,1,1,1]` | `[1,1]` | `(1−T)^2` |

The complete e/f profiles for every tested prime and exact seven polynomial
cross-products are in the machine receipt. The report's source-level
comparison of the generic quadratic-residue rule to relative field splitting
is in [`h6-quartic-zeta-quotient-plan.md`](h6-quartic-zeta-quotient-plan.md).

## Provenance and execution

The executed checker was frozen at
`h6_quartic_zeta_quotient_attempt4.source`, SHA-256
`7139eb656580755af33ece151acb072bdc76ef3d8af60e47b6118cfd22f39a5f`.
The immutable result is [`h6_quartic_zeta_quotient_attempt4.json`](h6_quartic_zeta_quotient_attempt4.json),
SHA-256 `5d568a5830300ce24b1bb1411bc35c146f0241d414ba0832bd7db8d1d0d64f41`;
the original guarded output is
[`h6_quartic_zeta_quotient_attempt4.log`](h6_quartic_zeta_quotient_attempt4.log),
SHA-256 `6189260ca42474312ad5d3579fcdfedb3f60fd20adbe21b27ae86332b87202cd`.
The successful command was:

```sh
python3 automation/lean-formalization/guarded_build.py --timeout-seconds 900 -- \
  env PYTHONPATH=/tmp/unit-distance-flint python3 \
  lean-formalization/verification/sol-luna-20260923/numerical-audit/h6_quartic_zeta_quotient.py
```

Guard admission was 16.3 GiB host-available / 1.36 GiB cgroup headroom.
The checker-reported GP phase took `0.033771940` seconds; the entire wrapper
returned in approximately 7.01 seconds by tool polling. Peak RSS was
unavailable. PARI/GP was `/usr/bin/gp`, executable SHA-256
`96db9f9c75bcf665232278476bb752777086f6a86d1f645cb03a966987b96140`; a
post-run query with its documented `--version-short` flag reports version
`2.17.2`. The generated GP source hash is
`dffac4c86dc11f0b8c7e219bc684c5e608aea0e95de312c961f3bbab2194604d`.

The imported reference recurrence transitively loads python-flint 0.9.0
from `/tmp/unit-distance-flint`; this dependency was needed for Python module
imports only. It did not perform numerical arithmetic in this check. The
installation tree hash is
`1003f80b4b8a20a5b7f5aa2c9dea5fff6490ace53490d4a28cf5e0c35cbab6af`
(71 files, 25,419,377 bytes; Python 3.13.5). The full envelope is in
[`h6_quartic_zeta_quotient_attempt4-provenance.json`](h6_quartic_zeta_quotient_attempt4-provenance.json),
SHA-256 `74dc213dce6507c61c5931770ec7799ec8b0522b670c15f9dab7b63b559e850a`.

There is one metadata defect in the immutable attempt-4 receipt: its source
queried `gp -v`, which PARI/GP treats as an invalid option and answers with
usage text. The independent documented version query above corrects that
metadata only. The checker source was then changed only to use
`--version-short` and record the import-only python-flint tree; no coefficient
or local-factor formula changed. Reruns with that provenance-corrected source
were deferred three times with exit 75 because the shared lock or memory admission
was unavailable. The deferrals are preserved in
[`h6_quartic_zeta_quotient_attempt5.json`](h6_quartic_zeta_quotient_attempt5.json)
[`h6_quartic_zeta_quotient_attempt6.json`](h6_quartic_zeta_quotient_attempt6.json)
and [`h6_quartic_zeta_quotient_attempt7.json`](h6_quartic_zeta_quotient_attempt7.json)
with their logs; the current checker source SHA is
`1643a51379688ba6c1df0aee178f1759e16b8b4016e09c1394e648eabeee7905`.
The successful attempt-4 result remains the completed coefficient check.

For transparency, attempts 1–3 are preserved with their logs and receipts.
They respectively record a generated GP syntax error, a representation-type
mismatch in the row's bad-factor table, and a missing `PYTHONPATH` for the
import-only flint dependency. None of those attempts produced a coefficient
comparison; they do not affect the attempt-4 PASS.

## Mathematical scope

The coefficient equality is an exact finite arithmetic check conditional on
the proposed field identification. It is strong evidence that the H6 row's
local factors agree with the relative zeta quotient through the tested
range, and it independently checks the explicit seven local factors.
It does not by itself prove the all-prime equality of the Hecke L-function
and the zeta quotient, the conductor, gamma factor, root number, functional
equation, contour-shift growth hypotheses, complete AFE tail, or any global
bound for `H`. Those remain inherited analytic assumptions or separate proof
obligations.
