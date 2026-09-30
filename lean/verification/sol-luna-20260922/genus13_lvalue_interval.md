# Independent conductor-13 L-value enclosure

## Scope and provenance

This check encloses the real primitive quadratic Dirichlet value
`L(χ₁₃, 12001/12000)` from its Dirichlet series. It does not evaluate the
finite completion integral used by the genus Lean consumer, verify a genus
aggregate, or prove any part of hypothesis (H).

The coefficient sequence is computed as the Legendre symbol modulo 13. The
Lean source `GenusDirichletConductorsRun20260920.lean` defines
`commonChi13` from `primeQuadraticCharacter 13`, and
`GenusLunaRun20260922ConductorThirteen.lean` identifies the actual primitive
character of the conductor-13 genus row with that same quadratic character.
The script pins both source SHA-256 hashes and a compact fixture SHA-256
(`915c0020aa13ee97ce3544565d214e4c320e023e6fce4e7bfddd21fc6a6ad212`), and
asserts the explicit period `(1,-1,1,1,-1,-1,-1,-1,1,1,-1,1,0)`. If both
Lean sources are present, it checks their hashes and binding text. If they are
absent in a package extraction, it identifies the fixture as the source
binding record and does not claim a fresh Lean source comparison. The period
has sum zero and all partial sums have magnitude at most 2.

## Enclosure method

The script includes terms through `N=13000`, an endpoint of a full period.
Each logarithm is enclosed by range-reduced
`log(y)=2 atanh((y-1)/(y+1))`, with the geometric remainder bounded using
denominators at least `2K+1`. It encloses `exp(-log(n)/12000)` by odd/even
alternating Taylor truncations. Every finite interval is rational; term
endpoints are rounded outward to denominator `10^40` before accumulation.

After `N`, summation by parts and the period partial-sum bound give
`|tail| ≤ 2 (N+1)^(-s) < 2/13001`, since `s=12001/12000 > 1`. This supplies a
two-sided rational enclosure of the full convergent L-series. The result is
numerical evidence from this independent exact-rational computation, not a
Lean theorem.

The current conductor-13 genus progress report gives a Lean bound by the
finite completion integral but records no explicit numerical allowance for
this row. Therefore this check has no pinned manuscript row allowance to
compare against; it reports only the L-value enclosure.

## Reproduction and result

Run through the repository's shared resource guard:

```sh
python3 automation/lean-formalization/guarded_build.py \
  --wait-seconds 300 --timeout-seconds 900 -- \
python3 lean-formalization/verification/sol-luna-20260922/genus13_lvalue_interval.py
```

Final guarded run after the outward-display correction: admitted with 16.9
GiB available and exited 0. Both pinned Lean source hashes and binding
assertions matched. The exact rational endpoints are unchanged; the printed
15-place decimals are now exact outward floor/ceiling values.

Pinned source hashes:

- `GenusDirichletConductorsRun20260920.lean`:
  `da1f113fb627a0e64651d1b5998f453f7d0e452771ea0a1f18ada752ca9b3a77`
- `GenusLunaRun20260922ConductorThirteen.lean`:
  `110cc2883052d0cfa0a18f048c809a91154365cf31039e34a0c8c04e83694950`
- Compact source fixture:
  `915c0020aa13ee97ce3544565d214e4c320e023e6fce4e7bfddd21fc6a6ad212`
- Checker script:
  `66b87a8d0967228dfd0fe0ece225bb0261438ecefba0eb821dbbd39c006b5460`

The emitted exact enclosure is

```text
[6626074990486226788823560073231467744757/10^40,
 6629151676894969563112000348433037289210/10^40]
```

with outward-rounded 15-place decimals
`[0.662607499048622, 0.662915167689497]`. The tail radius supplied to the
endpoint accumulator is `ceil(10^40 * 2/13001)/10^40`,
which is outward from the proven strict bound `|tail| < 2/13001`. The finite
term interval endpoints are also rounded outward at scale `10^40`.

No corresponding conductor-13 row allowance is explicitly given in the
pinned genus progress materials, so no manuscript allowance comparison is
claimed. This checks one actual character L-value via its Dirichlet series;
it does not evaluate the completion integral or close the genus aggregate.
