# Source analysis: the all-n degree-two Artin coefficient majorant

## Result

For a finite-image, two-dimensional complex Artin representation, the bound
`|a_n| ≤ d₂(n)` follows from three exact ingredients:

1. At every rational prime `p`, including ramified primes, the Artin local
   factor is formed from the action of Frobenius on inertia invariants
   `V^{I_p}`. Its dimension is `0`, `1`, or `2`. Pad its eigenvalue list to
   two entries with zeros, giving `α_p, β_p` with `|α_p|, |β_p| ≤ 1`.
2. The coefficient of `T^k` in
   `((1 - α_p T)(1 - β_p T))⁻¹` is
   `b_{p,k} = ∑_{j=0}^k α_p^j β_p^(k-j)`. The triangle inequality gives
   `|b_{p,k}| ≤ k+1 = d₂(p^k)`.
3. The global Dirichlet coefficients are multiplicative and their local
   `p`-power coefficients are these `b_{p,k}`. Multiplicative factorization
   then gives `|a_n| ≤ ∏_{p^k || n}(k+1)=d₂(n)` for every `n>0`; `a_0=0`
   handles zero.

Finite image is sufficient for the eigenvalue condition: Frobenius has finite
order on the inertia-invariant subspace, so its eigenvalues are roots of unity.
The local inequality itself only needs the two eigenvalue norm bounds and the
local coefficient formula. The all-prime scope matters: at a ramified prime,
`V^{I_p}` may have smaller dimension. Padding by zero handles dimensions one
and zero; it does not permit silently omitting a ramified Euler factor.

## Lean lemma shape

The local inequality is a small finite-sum lemma. This Lean-shaped draft is
not compiled in this note:

```lean
private def twoEigenEulerCoeff (α β : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1), α ^ j * β ^ (k - j)

theorem norm_twoEigenEulerCoeff_le (α β : ℂ) (k : ℕ)
    (hα : ‖α‖ ≤ 1) (hβ : ‖β‖ ≤ 1) :
    ‖twoEigenEulerCoeff α β k‖ ≤ (k + 1 : ℝ) := by
  -- triangle inequality; each of the k+1 summands has norm ≤ 1
  ...
```

A reusable global companion can be stated for
`a : ArithmeticFunction ℂ`: assume `a.IsMultiplicative` and, for each prime
`p` and exponent `k`,

```lean
‖a (p ^ k)‖ ≤ ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 2)
  (p ^ k) : ℕ) : ℝ)
```

then `‖a n‖ ≤ (((ζ ^ 2) n : ℕ) : ℝ)` for every `n`. For `n ≠ 0`, the proof
is exactly the `multiplicative_factorization` pattern used in
`IdealCounting.idealCount_le_zeta_pow`; on prime powers,
`IdealCounting.zeta_pow_apply_prime_pow` evaluates `(ζ²)(p^k)` as
`Nat.multichoose 2 k = k+1`. The zero case follows from the arithmetic
function's `map_zero` field. Mathlib already supplies both cited lemmas and
`ArithmeticFunction.IsMultiplicative.multiplicative_factorization`.

To derive prime-power hypotheses from a two-dimensional Artin local factor,
formalize (a) its local factor as the reciprocal determinant on inertia
invariants, (b) a finite eigenvalue list of length at most two, (c) the
power-series coefficient formula above, and (d) the identification of these
local coefficients with the row's Euler coefficients. The latter is the row
matching obligation; it is not supplied by the generic inequality.

## What is already established for H6 mask 1586

There are two twists in the H6 mask-1586 sector, and their proof status must
not be merged.

### Twist `-1`, conductor 15015

The Lean development already proves the all-n majorant for the source-defined
actual factor. It defines `B = ℚ(√−35)`, `η = 17 + 2√−35`, and
`β = −η`; it proves the base degree is two, `N(η)=N(β)=429`, `β` is
nonsquare, and `B(√β)/B` has relative degree two. It records mask 1586,
twist `−1`, and conductor 15015 (`HeckeManuscriptMixedQuadratic1586ArithmeticRun20260920.lean:23–83, 125–135`).

The local all-prime theorem classifies the quadratic Euler factor as split,
inert, or ramified and assigns local sign `+1`, `−1`, or `0`
(`HeckeQuadraticEulerAllPrimes.lean:21–31, 99–110, 126–180`). The
row-1586 coefficient source applies this to every prime ideal of `B`, proves
each monomial weight has norm at most one, and bounds the coefficient norm by
the number of `B`-ideals of norm `n`
(`HeckeManuscriptMixedQuadratic1586QuadraticCoefficientsRun20260920.lean:95–115,
150–175`). Since `[B:ℚ]=2`, `idealCount_le_zeta_pow` gives the all-n bound
`quadraticSignCoefficients_norm_le_zeta_sq` at lines 177–187. The source
identifies the resulting Euler product with the actual quotient
`ζ_{B(√β)}/ζ_B`, including the ramified-prime local signs (lines 324–344),
then identifies these coefficients with the exact Dirichlet-inverse
`coefficients` (lines 350–436). In particular,
`coefficients_norm_le_zeta_sq` is already the desired global all-n result for
this defined quotient. It is an unconditional Lean theorem, unlike a finite
coefficient hash.

The dedicated class-field sources also construct the actual quadratic
ray-character for this `FactorField/BaseField` extension; the construction
is explicitly finite order (`Mixed1586RayArtinCharacterRun20260920.lean:1–17,
40–99`). The current majorant proof does not need a separate two-dimensional
Artin representation object: its norm-fiber argument is a more direct route.

### Twist `+1`, conductor 240240

The fresh H6 numerical row is the same mask and dimension with twist `+1`,
conductor 240240, and cutoff 3922. Its replay reconstructs a finite signed
coefficient vector, checks its hash and moment bins, and computes the pointwise
AFE kernel, but the report still lists the all-n `|a_n|≤d₂(n)` bound and row
factor identification among assumptions
(`numerical-audit/h6-mixed-quadratic-plan.md:7–25, 44–47`). Those finite checks
are not an all-n proof.

The existing Lean factor module uses `β=−η` (the `−1` twist); it does not
construct the `+1` extension `B(√η)` or prove equality with the `+1` row's
Euler factors at every prime. There is useful reusable input: `N(η)=429`
and the nonsquare proof for `β` already reduces nonsquareness to the rational
fact that 429 is not a square. A parallel `+1` construction should prove
`η` nonsquare, set `F₊=B(√η)`, and apply the generic all-prime quadratic Euler
identity and ideal-norm-fiber coefficient majorant. It must then match the
resulting quotient's local factors—including every bad/ramified prime—to the
H6 `+1` row. A finite vector hash through 3922 cannot discharge that identity.

## Separation from the finite coefficient hash

A hash and exact moment check certify a fixed vector prefix and its finite
linear statistics. They do not establish the local eigenvalue description
for every prime, multiplicativity, or the prime-power estimate for arbitrary
exponents. The all-n theorem requires the structural Euler-factor proof above
(or the existing ideal-norm-fiber proof for the `−1` quotient). Even after the
coefficient bound is established, the AFE still needs its separate conductor,
gamma factors, root number, functional equation, and complete deleted Euler
factors.

## Classification

- **Generic lemma:** the two-eigenvalue local coefficient inequality follows
  unconditionally from `‖α‖,‖β‖≤1`; the global `d₂` inequality follows with
  multiplicativity and the prime-power coefficient bounds.
- **Already proved:** the all-n `d₂` bound for the source-defined H6 mask-1586
  twist-`−1` quotient, including ramified local factors.
- **Not yet shown for the numerical twist-`+1` row:** an actual `B(√η)` Lean
  factor module and its all-prime identification with that row. No finite
  coefficient hash can replace these proofs.
- **No Lean build was run** for this source analysis or the uncompiled local
  lemma sketch.
