# Static review of the common-level conductor-13 enclosure

## Verdict and scope

The factor signs, correction direction, rational interval multiplication, and
logarithm interval directions in
`genus13_common_level_interval.py` are mathematically consistent. I did not
rerun the algorithm. This review is a static audit of the stated selected-prime
correction applied to the already reviewed primitive interval. It does not
identify the value with a slot in the manuscript's 128-factor product, supply
a row allowance, or prove the genus aggregate or (H).

## S' primes, character values, and Euler-factor direction

The current Lean definitions give `selectedRationalPrimeSet` as the first
seven `selectedPrime` values; `selectedPrime` is `Witness.primes`, whose first
seven entries are `2,3,5,7,11,13,17`. Independently, the common-level Lean
theorem `selectedPrimeValues_eq_commonGenusPrimeFactors`, together with
`commonGenusModulus_primeFactors`, identifies this set with the prime factors
of the common modulus and proves it is exactly
`{2,3,5,7,11,13,17}`. For the primitive quadratic character modulo 13, the
Legendre values at these primes are
`(-1,1,-1,-1,-1,0,1)`, as asserted by the checker. In particular, 13 is the
primitive conductor and its local character value is zero.

The primitive local Euler factor is
`(1 - χ₁₃(p) p^(-s))^(-1)`. Deleting that factor from the primitive Euler
product multiplies the primitive `L`-value by its inverse,
`(1 - χ₁₃(p) p^(-s))`. This agrees with the imprimitive Lean definition and
the checker. Thus the code uses `1+p^(-s)` for each selected `χ=-1` prime,
`1-p^(-s)` for `χ=1`, and `1` at `p=13`; these directions are correct.

## Rational intervals and logarithm direction

For each selected prime, the checker writes
`p^(-12001/12000) = p^(-1) exp(-log(p)/12000)`. Its base logarithm interval
and alternating Taylor bounds yield an outward interval `[power_lo,power_hi]`.
The transformations are monotone in the indicated directions:

- if `χ=1`, then `1-power` lies in
  `[1-power_hi, 1-power_lo]`;
- if `χ=-1`, then `1+power` lies in
  `[1+power_lo, 1+power_hi]`;
- if `χ=0`, the factor is exactly 1.

All factors and the primitive `L` interval are positive, so endpoint products
give an enclosure without mixed-sign corner cases. The checker rounds the
lower and upper products down and up, respectively, at denominator `10^40`.
It verifies the resulting interval contains the unrounded rational endpoint
products.

The deleted value interval is positive and below 1. Since `log` is increasing,
its lower endpoint is `-upper(log(1/value_lo))` and its upper endpoint is
`-lower(log(1/value_hi))`. The code uses exactly this reversed direction,
then rounds outward. The reciprocal arguments are greater than 1; the
particular computed endpoints are below 2, as required by the documented
range-reduced log use.

## Provenance boundary

The final checker pins hashes for the primitive Euler, imprimitive Euler,
common-level bridge, selected-set, and genus-deletion Lean files, and checks
the relevant theorem-name/text anchors when the full research source set is
present. It also checks the transitive definitions when present:
`SigmaCutAbsoluteGenus.lean` binds `selectedPrime` to `Witness.primes`, and
`Witness.lean` supplies the prime array. The research-tree run matched all
five core pins and both optional pins. In the simulated archive layout, the
five core research sources were absent, but both optional `UnitDistance/`
files were found and matched their hashes and text anchors. The checker
reports this source-binding mode explicitly. The archive-layout run directly
checks the prime-array definitions but is not a rebuild of the missing
selected-set and common-level Lean theorems; those expected identities remain
bound by their embedded source hashes rather than freshly compared there.

The primitive subchecker now prints its lower endpoint with outward rounding
(`0.662607499048622`; its upper display is `0.662915167689497`). The exact
rational endpoints used by the correction are unchanged. The corrected
common-level checker passed final guarded research-tree and simulated
archive-layout runs, both exit 0; the report records the respective admission
memory and source-binding modes.

The current selected-prime list and χ values agree with the Lean definitions
and the pinned `selectedPrimeValues_eq_commonGenusPrimeFactors` theorem in the
full research source tree. No current set-value error was found. The fallback
does not claim fresh checks of absent core Lean sources and is not a Lean
build or replay.

The optional source hashes are:

- `SigmaCutAbsoluteGenus.lean`:
  `33a4021d0b89643e1d79eff20f93aee9f5c5df548e9ec207c3ced0fef152235e`
- `Witness.lean`:
  `56143fbf788d3d1a0e3fb0e8f4de76e5a8403b35fa74c22cfae43605ab7f8c81`

The reviewed final checker hash is
`dd72c0d242c2f979dc1a054e496ea5d7dcaa156be0e10ba093a29b88622bfada`; it pins
the corrected primitive checker hash
`66b87a8d0967228dfd0fe0ece225bb0261438ecefba0eb821dbbd39c006b5460`.
