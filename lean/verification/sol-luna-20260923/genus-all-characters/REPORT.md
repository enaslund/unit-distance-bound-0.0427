# Full 128-row genus numerical replay, September 23

## Result and scope

The guarded [replay](genus_full_direct.py) passed for every one of the 128
seven-bit quadratic masks at `sigma = 12001/12000`. It reconstructed each
fundamental discriminant from `[-1,2,3,5,7,11,13]`, built a primitive real
Conrey character, and checked **all 677,376 values across their periods**
against a separate Jacobi/Kronecker implementation. It then freshly called
FLINT/Arb's Dirichlet `L` evaluator, recomputed the seven selected-prime
deletion factors, and added the 128 log moduli. Every fresh primitive value
and deleted log lies strictly inside its archived dyadic row enclosure.

At 512-bit Arb precision, the resulting sum was

```text
7.3375781308465302206470681816905033421280800089552434789664879...
```

with a reported radius below `2.1e-144`. Its outward ball is strictly below
both the inherited normalized genus receipt's upper endpoint, after
multiplication by 128, and the factor-table allowance
`7.337578130846530221`. The machine-readable [result](genus_full_direct.json)
contains each row and the full ball. The χ13 row, mask 64, has deleted value
`0.93321598576904842317...` and log `-0.06911860892473417959...`;
the χ7 row, mask 17, has deleted value `0.98471096982429119764...`.
These match the direction of the separate Lean one-factor estimates.

This checks a complete numerical *genus* family. It does **not** prove (H):
the four non-genus analytic families, relative Artin/Hecke identification,
prime census, and derivative debit are separate inputs. The fresh replay and
the inherited genus receipt both use FLINT's Dirichlet L backend. Thus the
character construction, entire-period cross-check and output recomputation
are independent of the inherited script and saved values, while the analytic
L-evaluation algorithm is a shared trusted numerical library. The archived
intervals are loaded only after the fresh character and value calculation,
for comparison.

## Connection to Lean and remaining proof

The mask ordering, radicands and fundamental-discriminant formula are exactly
those in `GenusDirichletRowDataRun20260920`; the actual conductor equality is
checked in `GenusDirichletConductorsActualRun20260920`. Lean also identifies
each coherent genus Euler value with a primitive Dirichlet L-series times the
selected-prime deletion factor in
`GenusDirichletPrimitiveActualRun20260920`. The read-only
[Lean bridge review](lean-bridge-review.md) found no mask or sign mismatch,
but identified a missing **all-mask pointwise theorem** equating Lean's
primitive character with the script's Kronecker/Conrey character, including
nonunits and selected primes. Only individual rows such as χ13 and χ7 have
that identification. The numerical result therefore cannot be asserted as a
Lean bound for the whole actual genus product yet. A new Lean rowwise
interface, `ZetaSolGenusRowReceiptBridge20260923.lean`, is being checked
separately; its per-row numeric bounds remain explicit hypotheses.

The [independent code review](review.md) found no blocking error in the
Jacobi algorithm, CRT character numbering, interval comparisons or source
pins. It separately flagged the shared FLINT backend noted above.

## Finite local-atom bridge check

The separate [atom checker](genus_atom_bridge_check.py) passed over all 128
masks and all 677,376 residue classes in their conductor periods, including
zero and all nonunits. It compared the explicit 2-primary atom times selected
Legendre atoms against a standalone Kronecker-symbol routine, then checked
every value against the corresponding Conrey character from python-flint
0.9.0. It counted 512,211 zero values. Python was 3.13.5; checker wall time
was 4.261 seconds. All 10 pinned Lean input hashes and both local reference
hashes verified in the final run.

The admitted run used the shared lock
`/tmp/lean-formalization-1000.build.lock`, host admission/stop thresholds of
10/6 GiB, and cgroup admission/stop thresholds of 1/0.5 GiB. It was admitted
with 16.5 GiB host available and 1.13 GiB cgroup headroom and exited zero. An
earlier admitted attempt at the same reported headroom exited 1 because
python-flint returns an `acb` from `character(n)`, which cannot be converted
to `int`. The checker now compares that value directly with the expected
integer and hashes the checked integer. Three previous attempts had deferred
at guard admission before launching the checker.

Checker SHA-256:
`a3200ec3b0ce2a3f73efb4c840043dfa0484318d3b4372e9d3f00330d90857ef`.
Result JSON SHA-256:
`98780685630ce51bfef3eb1bb4d39b67c313095e7f028d1f35e782dde33ed6de`.
The per-mask counts and digests are in
[`genus_atom_bridge_check.json`](genus_atom_bridge_check.json). This is a
finite-period arithmetic check of the paper-level atom formula. The universal
Lean theorem identifying every assembled primitive character with the
Kronecker formula for all integer arguments remains open.

## Reproduction and provenance

Run from the repository root, with `python-flint 0.9.0` available at the
documented local `PYTHONPATH` or in the interpreter environment:

```sh
PYTHONPATH=/tmp/unit-distance-flint python3 automation/lean-formalization/guarded_build.py \
  --lock-path /tmp/lean-formalization-1000.build.lock --timeout-seconds 900 -- \
  python3 lean-formalization/verification/sol-luna-20260923/genus-all-characters/genus_full_direct.py \
  --output lean-formalization/verification/sol-luna-20260923/genus-all-characters/genus_full_direct.json
```

The first successful guarded run admitted at 17.6 GiB host available and
1.58 GiB cgroup headroom, finished in 18.94 seconds (18.783 seconds inside
Python), and exited zero. An initial guarded 256-bit run exited 1 at the row-0
archived-interval comparison: the stored dyadic endpoints are much narrower
than their decimal displays. Raising the fresh evaluation to 512 bits made
every strict interval comparison pass; no interval was widened or changed.
Both attempts used the required shared lock. The pre-portability script
and result hashes were respectively
`c4618ac182c0754fbcde3747b9e5c5b02edd44097ac8be642424129b561e234d`
and `529c95c99fa17f6dfe8f04f226c40e47fc098d7a15e566cca8ecb9baf2c9465e`.

The script now also accepts a hash-pinned compact
[comparison fixture](genus_comparison_fixture.json) when the research source
tree and archived JSON are absent from an extracted candidate package. In
the research checkout it checks every present Lean source hash and verifies
the compact fixture is an exact projection of the archived JSON. A
standard-library projection check passed for all 128 rows; an independent
[static portability review](portable-fixture-review.md) found the package
path and hash logic consistent. The **updated script passed a second guarded
full 128-row replay**: admitted with 17.0 GiB host available and 1.39 GiB
cgroup headroom, finished in 18.94 seconds (18.825 inside Python), exit 0.
It recorded `comparison_mode=archive_and_fixture`, all four pinned Lean
source hashes verified, archived JSON verified, and the same strict interval
and allowance results. Its SHA-256 is
`24f0a4cfa2b6eb4b3ad390ce62571b1a23b7978d6d660733e1328dd1b1f299e5`;
the current [result JSON](genus_full_direct.json) SHA-256 is
`304407c46d2172918d2256c84eece24d4b27f1b1988ae586f7eacace806df15e`.

The package-only fixture mode has **not yet been run from an extracted
candidate**. It is designed to record absent original Lean sources and
archive explicitly; the package snapshot and script's fixture SHA would
bind the comparisons, while no source-hash verification would occur in that
mode. A later extracted-package smoke is needed before claiming portability
was executed.
