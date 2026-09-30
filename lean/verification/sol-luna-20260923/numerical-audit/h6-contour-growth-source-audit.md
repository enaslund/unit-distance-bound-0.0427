# H6 contour growth and source-factor audit

This note separates the analytic requirements of the degree-two H6
exponential-integral (expint) contour argument from facts proved for the
Lean-defined row-1586 relative zeta factor. The checked Lean factor and the
numerical `+1` row must not be identified without a further representation
and row-matching theorem.

## Contour shift: required analytic input

The independent expint derivation sets
`Λ(w) = 2 t₀^(-w) Γ(w) L(w)` and uses the two-kernel
`K_s(w) = 1/(w-s) + 1/(w+s-1)`; see
[`h6-expint-formula-independent-review.md`](h6-expint-formula-independent-review.md),
lines 12–44. On shifting the contour from `Re(w)=c` to `Re(w)=1/2`, a
rigorous residue argument requires:

1. `Λ` is holomorphic on the contour rectangle (entire completion is a
   sufficient hypothesis), and the stated functional equation is exactly
   `Λ(1-w)=+Λ(w)`.
2. There are no additional poles in the rectangle beyond the kernel pole
   `w=s` whose residue is used. The pole `w=1-s` is left of the centered line
   for the stated `s>1/2`.
3. The horizontal integrals vanish as their heights tend to infinity, and
   the centered-line integral exists. A direct sufficient condition is a
   polynomial vertical-strip estimate
   `|L(σ+it)| ≤ C(1+|t|)^A`, uniformly for `1/2 ≤ σ ≤ c` and large `|t|`.
   Stirling's estimate for `Γ(σ+it)` supplies exponential decay
   `e^(-π|t|/2)` times a power of `|t|`; `t₀^(-w)` is bounded in modulus on
   this finite strip, and `K_s(w)=O(1/|t|)`. These estimates imply both
   horizontal-edge decay and absolute convergence on the centered line.

One standard way to obtain the strip estimate is to combine a Dirichlet-series
bound on a right boundary with the functional equation on a reflected left
boundary, then apply Phragmén–Lindelöf under an explicit admissible growth or
finite-order hypothesis. The exact polynomial strip bound is the clean
sufficient premise; “finite order” should be accompanied by the conditions
needed for that Phragmén–Lindelöf step.

In particular, **entireness and the functional equation alone do not justify
the contour shift**: they do not state horizontal-edge decay. This gap is also
identified in the independent derivation at lines 53–70 and the target-sigma
plan at lines 39–51.

## What the checked Lean source establishes

[`HeckeManuscriptMixedQuadratic1586.lean`](../../../UnitDistance/HeckeManuscriptMixedQuadratic1586.lean)
defines the literal factor as
`dedekindZeta FactorField / dedekindZeta BaseField` (lines 66–69), with its
coefficients defined from the genuine ideal-count sequences (lines 43–59).
The file specifies `MellinNormalizationObligation` and a separate
`ThetaReflectionObligation` (lines 118–132); these are not silently assumed
by a theorem there.

[`HeckeManuscriptMixedQuadratic1586QuadraticCoefficientsRun20260920.lean`](../../../UnitDistance/HeckeManuscriptMixedQuadratic1586QuadraticCoefficientsRun20260920.lean)
proves absolute L-series summability for `Re(s)>1` (lines 189–205 and
414–420), identifies the coefficients with the local quadratic-sign
coefficients (lines 406–420), proves the real-half-line factor/L-series
identity (lines 422–428), and gives the degree-two divisor majorant
(lines 178–187 and 430–436). This is enough for the right-hand Dirichlet
series and the coefficient-side smoothing estimates. It does not give a
vertical-strip bound for `L(σ+it)`.

[`HeckeManuscriptMixedQuadratic1586MellinRun20260920.lean`](../../../UnitDistance/HeckeManuscriptMixedQuadratic1586MellinRun20260920.lean)
proves the actual theta Mellin normalization on `Re(s)>1` and explicitly
states that it does not prove theta reflection / the functional equation
(lines 8–18, 111–153). The generic balanced Mellin theorem in
[`HeckeThetaMellinTruncation.lean`](../../../UnitDistance/HeckeThetaMellinTruncation.lean)
is conditional on a theta-transform input; it does not establish the
transform for this row.

The source module identifies this checked example as sector 1586, base field
`Q(sqrt(-35))`, and conductor 15015 (source lines 10–18). The arithmetic
source explicitly calls it the twist `D=-1` row:
[`HeckeManuscriptMixedQuadratic1586ArithmeticRun20260920.lean`](../../../UnitDistance/HeckeManuscriptMixedQuadratic1586ArithmeticRun20260920.lean),
line 41. By contrast, the H6 expint plan evaluates sector 1586, twist `+1`,
with conductor 240240 and states that its primitive completion, FE, conductor,
gamma signature, and root number `+1` are assumptions attached to the pinned
numerical row; see [`h6-target-sigma-expint-plan.md`](h6-target-sigma-expint-plan.md),
lines 5–7 and 39–51. Finite coefficient agreement or sharing the sector mask
does not identify those two factors.

## Missing bridge for H6 `+1`

For the Lean-checked `D=-1`, conductor-15015 quotient, the remaining analytic
source theorem is a proof of its actual theta reflection (or an equivalent
matched completed functional equation), together with sufficient growth to
justify the contour move. To use the numerical `+1`, conductor-240240 row,
there is an additional prerequisite: identify that numerical row's
representation/Hecke character with a source-defined factor, and prove its
conductor, archimedean gamma data, root number, coefficient sequence, and
completion agree. Only after that identification can a source-specific theta
reflection or analytic continuation theorem discharge the numerical row's
FE and contour-growth premises. None of these identifications follows from
the checked `D=-1` factor or from its coefficient and Mellin-normalization
theorems.

This is a source-only audit; no Lean build or numerical replay was run.
