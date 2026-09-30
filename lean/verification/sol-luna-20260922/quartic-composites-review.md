# Source review: quartic composite coefficient checker

Reviewed `quartic_field_composites_check.py` without executing it. I found no
factorization or coverage bug in the loop over `1 ≤ n ≤ 981`.

The script skips exactly the integers divisible by one of `2, 3, 5, 7, 11,
13`. Every remaining prime factor is at least 17, so an eligible prime can
occur at most twice in an integer at most 981 (`17^3 = 4913 > 981`). The only
eligible prime squares in range are `17², 19², 23², 29², 31²`, matching the
`square_cases == 5` guard. Thus the loop needs only the local coefficients at
`p` and `p²`. `factor_good` divides out those exponents, multiplies local
coefficients across distinct primes, returns `None` for an uncovered prime,
and raises for exponent at least three or for a missing square coefficient.
The `checked + skipped == limit` guard together with the per-`n` comparison
covers every integer in the interval.

For a two-dimensional Frobenius representation, the Euler coefficient at
`p²` is `(tr(Frob_p)^2 + tr(Frob_p²))/2`. The root-count differences in the
script supply the two traces when the polynomial models are separable at `p`;
the parity check certifies integrality. The quadratic extension construction
uses a nonsquare modulo odd good `p`, so it represents `F_(p²)`.

The checker now includes an irreducibility witness. Write
`α = twist * (x + y√a)` in `F = ℚ(√a)`, so the displayed quartic is
`(X² - α)(X² - conjugate(α))`. Its checked constants imply
`twist = -1`, `x = 17`, and `y² = 4`, hence `y ≠ 0` and
`√a = (α/twist - x)/y` lies in `ℚ(u)` for a root `u` with `u² = α`.
The check gives `N_F/ℚ(α) = c = 429`; since 429 is not an integer square,
it is not a rational square. If `α` were a square in `F`, its norm would be
a rational square. Thus `X² - α` is irreducible over `F`, and because
`F ⊂ ℚ(u)`, the root has degree four over `ℚ`. This proves irreducibility
of the quartic. The explicit `y ≠ 0` step is essential to this inference;
the script now tests it alongside `a < 0` and the nonsquare norm.

The remaining mathematical dependency is the analytic-row identification:
the quartic-minus-quadratic root-count difference is the trace of the
corresponding difference of permutation representations, but the checker
does not prove that this is the two-dimensional representation defining the
selected mixed quadratic row (including its twist). Root counts then give
the desired row's Artin traces only after that identity is established.
The check remains a finite comparison with the pinned row; it does not prove
a global Artin factorization.

Prime 17 is not in the field checker's ramified set, so it is included even
though the manuscript row records a special local denominator at 17. This is
consistent with the claimed scope (unramified coefficients supported away
from `2,3,5,7,11,13`), but should not be described as an Euler product with
all manuscript-selected factors deleted.
