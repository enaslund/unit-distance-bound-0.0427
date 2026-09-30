# Conductor-13 selected-prime-deleted value enclosure

## Result

At `s = 12001/12000`, the exact-rational checker encloses the selected-prime
correction

```text
C = ∏_{p ∈ {2,3,5,7,11,13,17}} (1 - χ₁₃(p) p^(-s))
```

using the values `χ₁₃(2,3,5,7,11,13,17) = (-1,1,-1,-1,-1,0,1)`. Its outward
rational enclosure is

```text
[14080724419654254165811985621882323089537/10^40,
 1760090552456781800596307348959213937151/1250000000000000000000000000000000000000]
```

Multiplying this by the already checked primitive-series interval gives the
selected-prime-deleted value enclosure

```text
[9329993592499974339406808547917501264903/10^40,
 9334325789844694771007291201103181530277/10^40]
```

Its outward-rounded 15-place display is `[0.932999359249997, 0.933432578984470]`.
The value is positive, so the same rational interval machinery gives

```text
log |L_deleted| ∈
[-693507648981614878769788500433829922907/10^40,
 -34443271256929887925112709859299635267/500000000000000000000000000000000000000]
```

or `[-0.069350764898162, -0.068886542513859]` with outward-rounded 15-place
decimals.

## Method and scope

[`genus13_common_level_interval.py`](genus13_common_level_interval.py) reruns
the existing rational period-series checker, consumes its exact primitive
interval, and encloses each `p^(-12001/12000)` using the existing atanh
logarithm bounds and alternating Taylor bounds for `exp(-log(p)/12000)`. All
endpoint products and logarithm bounds are exact `Fraction` arithmetic;
rounding is outward at scale `10^40`.

The primitive checker pins the character period and its source identity. This
checker additionally pins the primitive Euler, imprimitive Euler, common-level
bridge, selected-prime set, and genus deletion sources by SHA-256 when the full
Lean research sources are present. It requires either all pinned Lean sources
or none: with all present it checks hashes and binding text; with all absent it
reports fixture/source-hash-bound mode and makes no fresh Lean-source check.
The pinned Lean sources identify the corrected value as the actual common-level
conductor-13 genus-character `LFunction` at this abscissa. Two transitive
provenance sources are checked independently when present: `SigmaCutAbsoluteGenus.lean`
binds `selectedPrime` to `Witness.primes`, and `Witness.lean` pins the prime
list. These optional pins are independent because a packaged source tree may
contain `Witness.lean` without `SigmaCutAbsoluteGenus.lean`. Their lookup checks
the package-relative `HERE.parents[1] / UnitDistance` location as well as the
research-tree path. The numerical
enclosure itself is a Python exact-rational computation, not a Lean theorem.

This does not identify the value with a particular `genusLinearEulerValue`
slot in the manuscript's 128-factor product, and it does not establish a
per-row allowance. It makes no such allowance comparison: the published
analytic table records an aggregate allowance for all linear factors, not a
conductor-13 row allowance.

## Verification receipt

The guarded command was

```sh
python3 automation/lean-formalization/guarded_build.py \
  --timeout-seconds 900 --wait-seconds 300 -- \
  python3 lean-formalization/verification/sol-luna-20260922/genus13_common_level_interval.py
```

The final research-tree run was admitted with 17.1 GiB available and exited 0
in about 5 seconds. It reported that all five pinned Lean research sources
and both optional provenance sources were present and matched their hashes
and text anchors. A simulated archive-11 layout, with the checker tree under
`verification/` and both optional Lean files under the sibling `UnitDistance/`,
was admitted with 17.0 GiB available and exited 0 in about 6 seconds. It
reported fixture/source-hash-bound mode for absent research identity sources
and independently matched both optional provenance hashes and text anchors.
The primitive subchecker exited 0 in both runs. Current checker SHA-256:
`dd72c0d242c2f979dc1a054e496ea5d7dcaa156be0e10ba093a29b88622bfada`.
The primitive checker SHA-256 is
`66b87a8d0967228dfd0fe0ece225bb0261438ecefba0eb821dbbd39c006b5460`.

Pinned Lean source hashes:

- `ZetaLunaConductorThirteenEulerRun20260922.lean`:
  `6a2ae54fec9ee54bf780e126a431dad54316f58a8fbf416b1f1905637b127422`
- `ZetaLunaConductorThirteenImprimitiveEulerRun20260922.lean`:
  `1b9b2e7b97d56f77860e7afc4be7cb6a831053a4f2d06fd9d7260ece44689ffd`
- `ZetaLunaConductorThirteenCommonLevelRun20260922.lean`:
  `2ea6b772812ab2ac373a36cdc1cae0945878ba1fc95f6b2cd23b81be97ea6c42`
- `FixedZetaRetainedRationalFactorsAstra.lean`:
  `19da60338e59cf662e90a8345bc7965536e865a62d20d08955fcab9b21012d93`
- `GenusDirichletPrimitiveRun20260920.lean`:
  `6621fce9ac5c04a855c8e79d9ca0005d6c63a18cd87ca6b14e68bbc166fff99e`

Optional provenance pins, checked separately when each source is present:

- `SigmaCutAbsoluteGenus.lean`:
  `33a4021d0b89643e1d79eff20f93aee9f5c5df548e9ec207c3ced0fef152235e`
- `Witness.lean`:
  `56143fbf788d3d1a0e3fb0e8f4de76e5a8403b35fa74c22cfae43605ab7f8c81`
