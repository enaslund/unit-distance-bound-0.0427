# H6 mask-1586 twist `+1`: field-bridge feasibility and exact gaps

## Finding

A very small arithmetic bridge constructs the candidate plus-twist quadratic
extension `B(√η)/B`: the current source already proves `[B:ℚ]=2`, `N_{B/ℚ}(η)=429`,
and that 429 is not a rational square. The existing
`quadratic_primeFiber_factor_product` theorem is generic in the quadratic
extension and can therefore be specialized once `η` is proved nonsquare.

That small bridge does **not** by itself give the target row's all-n coefficient
bound. The existing coefficient realization is hard-coded to
`FactorField = B(√(−η))`, i.e. twist `−1`; its coefficient sequence, zeta
quotient, and final `d₂` theorem are all for that field. For twist `+1`, one
must define/identify `F₊=B(√η)`, realize its quotient coefficients, and prove
that the row's full Euler factors equal those of `ζ_{F₊}/ζ_B` at every rational
prime. A genericized coefficient theorem would avoid duplicating the current
roughly 400-line proof, but no such generic theorem is present at this
checkpoint.

## Exact Lean endpoints and the prospective plus specialization

The existing minus-twist quotient is concrete, not an abstract row symbol:

- `ManuscriptMixedQuadratic1586.BaseField` is `Extension (-35 : ℚ)` and
  `eta = ⟨17, 2⟩`, while `beta = -eta`. The instance
  `betaNonsquare` makes `FactorField := Extension beta` and
  `factorField_relative_degree` proves its relative degree is two
  (`HeckeManuscriptMixedQuadratic1586ArithmeticRun20260920.lean:24–78`).
- `ManuscriptMixedQuadratic1586.factor` is literally
  `dedekindZeta FactorField / dedekindZeta BaseField`; its
  `factor_local_euler`, `factor_eulerProduct_of_ne_zero`, and
  `factor_eulerProduct_real` expose the all-prime relative quotient
  (`HeckeManuscriptMixedQuadratic1586.lean:68–105`). The generic engine is
  `quadratic_primeFiber_factor_product` and
  `quadratic_relativeZeta_eulerProduct_real` in
  `HeckeQuadraticEulerAllPrimes.lean:132–231`. It covers ramified places too;
  `quadraticPrimeSignAll` is `+1` for split, `−1` for inert, `0` for the
  remaining case, with
  `norm_quadraticPrimeSignAll_le_one` (`:102–110`).
- The quotient's exact Dirichlet coefficient sequence is
  `coefficients`, defined as `idealCountComplex FactorField` times the
  Dirichlet inverse of `idealCountComplex BaseField`
  (`HeckeManuscriptMixedQuadratic1586.lean:42–59`). The independent
  norm-fiber sequence is proved equal by
  `coefficients_eq_quadraticSignCoefficients`; its all-natural-number bound
  is `coefficients_norm_le_zeta_sq`, giving the coefficient majorant
  `d₂(n) = (ArithmeticFunction.zeta ^ 2) n`
  (`HeckeManuscriptMixedQuadratic1586QuadraticCoefficientsRun20260920.lean:406–437`).
  This coefficient construction and these theorems mention the fixed
  `FactorField`, so they prove the −1 row only.

A plus field really can be introduced by a tiny specialization: prove
`eta_nonsquare` by applying `Algebra.norm ℚ` to a hypothetical square and
using `norm_eta = 429` plus `rational_429_not_isSquare`; install
`Fact (Nonsquare eta)`; set `PlusFactorField := Extension eta`; and use
`relative_finrank eta` for degree two. The generic
`quadratic_primeFiber_factor_product` then immediately gives the plus
extension's local factor at every prime ideal of `B`, including its ramified
case, with local sign norm at most one. So the all-prime *quadratic local
sign* statement is a short specialization.

That is not yet the all-rational-prime eigenvalue theorem for the H6 row. The
generic lemma's primes are `HeightOneSpectrum (𝓞 B)`, whereas the manuscript row
is indexed by rational primes and supplies degree-two Euler polynomials. One
must group all prime ideals of `B` above each rational `p`, prove their norm
and sign factors multiply to the row's polynomial, and cover both the seven
listed bad entries and every good `p`. In particular, row data at `p=17`
contains `(1−T)^2` although 17 does not divide conductor 240240; the factor
cannot be omitted as a putative deleted/ramified prime.

Once an all-prime local row identity and a finite-image two-dimensional
representation are available, the local coefficient estimate is elementary:
if the two local eigenvalues `α, β` have norm at most one, then
`‖∑_{j=0}^k α^j β^(k−j)‖ ≤ k+1`; the repaired standalone lemma in
`factor-inventory/TwoEigenEulerCoefficientBound20260923.lean` is intended to
prove exactly this local inequality. Multiplicativity would then give
`|a_n|≤d₂(n)` for row coefficients. However, the current coefficient module
instead proves the same bound for the **relative zeta quotient** by counting
ideals in norm fibers. Genericizing its `quadraticSignCoefficients`
construction and norm-fiber proof to a variable quadratic `K/B` is another
valid route, but it is a substantial refactor of that module, not a short
plus-field wrapper. Either route still needs the quotient-to-row local
identification. No existing theorem supplies the plus row's all-rational-prime
local eigenvalues or equality of its coefficient sequence to that quotient.

## Small candidate field bridge (source-level sketch; uncompiled)

The current arithmetic source defines `eta = ⟨17,2⟩`, proves
`Algebra.norm ℚ eta = 429`, and proves `¬ IsSquare (429 : ℚ)`
(`HeckeManuscriptMixedQuadratic1586ArithmeticRun20260920.lean:38–62`). Thus
the existing proof of `beta_nonsquare` at lines 64–72 can be adapted verbatim:

```lean
theorem eta_nonsquare : Nonsquare eta := by
  intro x hx
  apply rational_429_not_isSquare
  refine ⟨Algebra.norm ℚ x, ?_⟩
  have hnorm := congrArg (Algebra.norm ℚ) hx
  rw [map_pow, norm_eta] at hnorm
  simpa [pow_two] using hnorm.symm

instance etaNonsquareFact : Fact (Nonsquare eta) := ⟨eta_nonsquare⟩

abbrev PlusFactorField := Extension eta

theorem plusFactorField_relative_degree :
    Module.finrank BaseField PlusFactorField = 2 := relative_finrank eta
```

The base field, `eta`, and nonsquare-429 proof already exist. This establishes
a literal quadratic extension with the expected plus radicand. It does not
prove the H6 Artin-row identification.

## What specializes immediately

`quadratic_primeFiber_factor_product` in
`HeckeQuadraticEulerAllPrimes.lean:132–180` is generic in fields `F,K`, an
algebra structure, and a proof `Module.finrank F K = 2`. It includes the
ramified case: the local sign `quadraticPrimeSignAll F K q` is `+1` for split,
`−1` for inert, and `0` in the remaining (ramified) case, and its norm is at
most one (`:99–110`). Once the plus field bridge above is compiled, this
lemma specializes directly to `F=BaseField`, `K=PlusFactorField` without
assuming unramifiedness.

The same local-sign construction feeds the existing row-1586 coefficient
proof, but that proof is specialized to `FactorField`:
`quadraticExponentWeight`, `quadraticSignCoefficients`, the norm-fiber bound,
and the final `coefficients_norm_le_zeta_sq` all mention the namespace's fixed
`FactorField` (`HeckeManuscriptMixedQuadratic1586QuadraticCoefficientsRun20260920.lean:31–36,
68–114, 150–187, 324–344, 350–436`). Its final theorem is all-n and
kernel-checked for those exact quotient coefficients. To reuse it for the
plus field, either:

1. refactor this module's coefficient construction and proof to parameterize
   the quadratic extension `K/F` with `[Module.finrank F K = 2]`, then
   specialize at `PlusFactorField`; or
2. add a plus-specific coefficient module mirroring the current construction,
   changing the field to `Extension eta` and retaining the same norm-fiber
   majorant argument.

The direct Artin-coefficient alternative needs an actual two-dimensional
finite-image representation for the plus row, proof of each local factor as
its determinant on inertia invariants, and multiplicativity of the row's
coefficient sequence. The new two-eigenvalue source proves only the elementary
local finite-sum inequality; it does not provide these field/row links.

## Exact H6 `+1` Euler data that must be matched

The H6 arithmetic input is pinned in the audit as
`h6-low-degree-arithmetic.json` SHA-256
`b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`
(`numerical-audit/h6-mixed-quadratic-plan.md:49–59`). The mask-1586, dimension-2
row with twist `+1` has conductor `240240` and cutoff `3922`; its listed local
Euler denominators are:

| Rational prime | Listed denominator polynomial |
|---:|---|
| 2 | `1` |
| 3 | `1 − T` |
| 5 | `1 + T` |
| 7 | `1 + T` |
| 11 | `1 − T` |
| 13 | `1 + T` |
| 17 | `(1 − T)^2` |

These are target data, not yet Lean equalities with the prime-fiber factors of
`B(√η)/B`. In particular, `17` appears in the listed bad-Euler table although
it does not divide conductor `240240`; its nontrivial `(1−T)^2` factor must
still be included in a complete local matching. The seven-prime check is
necessary but not sufficient: one also needs the good-prime identity for all
`p∉{2,3,5,7,11,13,17}`.

For each listed rational `p`, the required local proof should factor the
actual prime ideals `q|p` in `B`, identify their residue degrees, and determine
whether `η` is a square in the corresponding residue/local field or whether
the relative prime is ramified. Then multiply the base-prime local factors
`(1−ε_q (Nq)^{-s})^{-1}` across `q|p` and show the resulting rational Euler
polynomial equals the table entry. At `p=2`, this must prove the degree-zero
Euler factor `1`; at `p=17`, it must prove two linear factors `(1−T)`.
For `3,5,7,11,13`, it must prove the indicated linear sign. Existing
`Mixed1586*` local residue, conductor, and Artin modules all specialize to
`β=−η` and cannot be cited unchanged for `η` without a transported local
character theorem.

## Existing versus missing premises

| Claim needed for twist `+1` | Current status |
|---|---|
| Base field `B=ℚ(√−35)` has degree 2 | Proved in current arithmetic source. |
| `η=17+2√−35` has norm 429; 429 is nonsquare | Proved. The same norm argument proves `η` nonsquare with a short Lean lemma, not yet added/compiled. |
| `F₊=B(√η)` has relative degree 2 | Follows immediately after `η_nonsquare`; no such named field currently exists. |
| Generic quadratic local factor handles all base primes, including ramified | Proved generically in `HeckeQuadraticEulerAllPrimes`; specialization to a new `F₊` is routine once the field exists. |
| An all-n `d₂` majorant for the *defined* quotient `ζ_{F₊}/ζ_B` | No current plus-specialized theorem. The minus theorem's proof method generalizes, but its definitions are fixed to `FactorField=B(√−η)`. |
| Equality of the quotient's Euler factors with the H6 `+1` row at all primes | Missing. In particular, the seven listed primes `2,3,5,7,11,13,17` have no checked field-to-table comparison; good primes also need a uniform Artin/Frobenius identification. |
| Finite coefficient hash through cutoff 3922 | Numerically checked only; does not prove any all-n condition above. |
| Conductor/gamma/root number/functional equation/AFe deletion data for the target row | Separate AFE obligations; they remain necessary even after coefficient majorant and local row match. |

## Practical recommendation

The field bridge itself is a small, low-risk Lean leaf. It is useful groundwork,
but should not be presented as discharging the target `+1` row. The minimum
honest all-n endpoint is a plus-specific or genericized coefficient proof plus
a full local Euler-factor comparison to the H6 table. The existing `−1` proof
cannot simply be relabeled: `η` and `−η` define different squareclasses and
the table shows materially different factors at 2, 3, 5, 7, and 11. No Lean
build was run for this source-only investigation.
