# Review of the conductor-13 L-value enclosure

## Verdict and scope

I found no mathematical error in the coefficient identification, finite-term
interval directions, or tail estimate in
`genus13_lvalue_interval.py`. This is a source review only; I did not rerun
the numerical computation. The conclusion is limited to the displayed
primitive quadratic Dirichlet-series value at `s=12001/12000`. It does not
evaluate the genus completion integral, identify a manuscript row allowance,
or prove the genus aggregate or (H).

## Character and indexing

The pinned Lean source defines
`primeQuadraticCharacter q hq` by casting Mathlib's `quadraticChar (ZMod q)`
to complex values, and sets `commonChi13` to its common-level induction for
`q=13`. The pinned conductor-13 genus source proves
`conductorThirteen_primitive_apply`, identifying its actual primitive
character pointwise with `primeQuadraticCharacter 13`. Mathlib's pinned
`quadraticCharFun` is zero at zero, one on nonzero squares, and minus one on
other elements. The nonzero squares modulo 13 are
`1,3,4,9,10,12`; this gives exactly the script's period
`(1,-1,1,1,-1,-1,-1,-1,1,1,-1,1,0)`. Its sum is zero and its cyclic partial
sums have maximum absolute value 2. The code's `(n-1) % 13` index assigns
coefficient `χ(1)` to `n=1` and coefficient zero at multiples of 13.

Source hashes checked against the current tree:

- `GenusDirichletConductorsRun20260920.lean`:
  `da1f113fb627a0e64651d1b5998f453f7d0e452771ea0a1f18ada752ca9b3a77`
- `GenusLunaRun20260922ConductorThirteen.lean`:
  `110cc2883052d0cfa0a18f048c809a91154365cf31039e34a0c8c04e83694950`
- Mathlib `QuadraticChar/Basic.lean` defining `quadraticCharFun`:
  `8fc3190363fca042ba368ed92ed3f48c2dad8da0f2420256fc072e59e05515fb`

In a package lacking the Lean sources, the script validates its compact
fixture hash and reports fixture-only binding mode; it does not claim to
recheck those source files in that mode.

## Interval and tail audit

For each positive integer `n`, the code range-reduces
`n = 2^k y`, `1 ≤ y < 2`, and encloses `log(y)` from
`2 atanh((y-1)/(y+1))`. For mantissas and the separate value `y=2` used for
`log 2`, `0 ≤ t=(y-1)/(y+1) ≤ 1/3`. After `K=12` terms,
the omitted positive series is at most
`2 t^(2K+1)/((2K+1)(1-t^2))`, so the returned logarithm interval has the
correct direction. Adding `k` copies of the interval for `log 2` preserves
its endpoints.

The script asserts `0 ≤ x_lo ≤ x_hi < 1`, with
`x=log(n)/12000`. The alternating Taylor series for `exp(-x)` has decreasing
term magnitudes on this range. Its degree-7 odd truncation is a lower bound
and degree-8 even truncation an upper bound. Monotonicity then gives
`P_7(x_hi) ≤ exp(-x) ≤ P_8(x_lo)`. Division by positive `n` preserves the
interval. Exact `Fraction` arithmetic and floor/ceiling at scale `10^40`
round every term outwards; for a coefficient `-1`, the endpoint order is
reversed before accumulation.

The cutoff `N=13000` is divisible by 13, so the coefficient partial sum
through `N` is zero and the shifted tail partial sums are bounded by 2.
Summation by parts for the decreasing weights `n^(-s)` gives
`|tail| ≤ 2(N+1)^(-s) < 2/13001` at `s=12001/12000`. The script rounds
`10^40 * 2/13001` upward before widening both endpoints, so the final rational
interval is outward. The printed decimals are expressly display-only.

The exact fractions above imply the outward-rounded displayed decimal interval
`[0.662607499048622, 0.662915167689497]`. The script now rounds the lower
endpoint down explicitly; its earlier display rounded that endpoint inward.
The corrected script's final guarded run was admitted with 16.9 GiB available
and exited 0, printing those outward decimals. This formatting correction does
not change the exact rational endpoints or the mathematical enclosure.

The fixture hash is
`915c0020aa13ee97ce3544565d214e4c320e023e6fce4e7bfddd21fc6a6ad212`; the
reviewed corrected script hash is
`66b87a8d0967228dfd0fe0ece225bb0261438ecefba0eb821dbbd39c006b5460`.

## Independent Hurwitz-zeta corroboration

As a separate numerical cross-check, I evaluated the finite Hurwitz character
formula

```text
L(χ₁₃,s) = 13^(-s) * Σ_{a=1}^{13} χ₁₃(a) ζ(s,a/13)
```

which follows by grouping the Dirichlet series into residue classes
`n=13k+a`. The computation used `arb.zeta(s,a)` from `python-flint==0.9.0`
at 256-bit precision, with `s=arb(12001)/12000` and the checked period-13
coefficients. The system Python had no `mpmath`; the local python-flint
environment was at `/tmp/unit-distance-flint` and was not part of the source
package.

The guarded invocation admitted at 19.0 GiB and exited 0. Arb displayed

```text
[0.66276134519502450028304089195439797961328174790589336399818076146420
 +/- 3.12e-69]
```

This ball lies inside the exact period-series interval recorded above. It is
an independent-method corroboration using a special-function library, not a
replacement for or input to the rational certificate and not a Lean proof.
