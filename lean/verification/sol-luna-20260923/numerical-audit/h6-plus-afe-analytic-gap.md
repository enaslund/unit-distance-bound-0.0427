# H6 mask-1586 `+1` row: analytic AFE dependency map

Source-only audit; no Lean or numerical job was run. This records a theorem
target and the checked/missing inputs, without claiming a proof. In
particular, `HeckeManuscriptMixedQuadratic1586PlusFieldBridge20260923.lean`
is staged source with compilation pending; statements about its declarations
below describe the source, not a checked Lean result.

## Candidate theorem

For the mask-1586 rational twist `+1` row, the target conductor is
`Q = 240240`, gamma signature `[0,1]`, root number `+1`, and
`σ = 12001/12000`; the row’s cutoff is `N=3922` (the 32-row report gives the
row distribution). Put `t=2π/√Q` and
`E_v(x)=∫_1^∞ exp(-xu)u^(-v)du`. The candidate analytic statement is

`L₊(σ) = (t^σ/Γ(σ)) Σ_{n≥1} [aₙ E_(1−σ)(tn) + conjugate(aₙ) E_σ(tn)]`.

The normalization follows from
`Γ_R(s)Γ_R(s+1)=2(2π)^(-s)Γ(s)`, hence
`Λ₊(s)=Q^(s/2)Γ_R(s)Γ_R(s+1)L₊(s)=2t^(-s)Γ(s)L₊(s)`.
The plus sign in the dual sum uses root number `+1`; in general it is
multiplied by `ε`. The displayed real signed expression additionally uses
the replay’s real coefficient row. For the removed-factor target `L_S`, one
also needs the exact identity between `L₊` and `L_S` through the complete
listed bad-prime Euler denominators. The 32-row replay documents these
normalizations and assumptions at
[`h6-target-sigma-expint-plan.md`](h6-target-sigma-expint-plan.md), lines
21–51, and batch scope at
[`h6-all-quadratic-expint-plan.md`](h6-all-quadratic-expint-plan.md), lines
5–20, 29–44.

## Analytic hypotheses needed for the theorem

A Lean proof of the candidate identity can be organized around the contour
calculation in
[`h6-expint-formula-independent-review.md`](h6-expint-formula-independent-review.md),
lines 18–75. Its minimal source inputs are:

1. The actual `+1` factor has `L₊(s)=Σ aₙn^(-s)` with absolute convergence
   on some line `Re(s)=c>max(3/2,σ)`, and the displayed coefficients are the
   same coefficients as the factor’s good and bad Euler data.
2. The completion `Λ₊(s)=2t^(-s)Γ(s)L₊(s)` has the stipulated holomorphic
   continuation in the contour region and satisfies the conjugation-compatible
   FE with root number `+1`.
3. The horizontal contour edges vanish and the center integral converges.
   A sufficient premise is polynomial vertical-strip growth of `L₊` on
   `1/2≤Re(s)≤c`; the gamma factor then supplies exponential decay. An
   equivalent theta/Mellin derivation may discharge this premise directly.
4. The numerical upper additionally needs an all-`n` bound
   `|aₙ|≤d₂(n)`, so the exponential-integral tails are bounded by the proved
   `d₂` majorant; finite prefix checks do not prove this.

For all 32 rows, these facts must be established uniformly or specialized to
each twist with its exact conductor, FE/root number, Euler factors, and
coefficient bound. The present 32-row receipt is explicitly conditional on
them.

## Available source modules and scope limits

* The staged source
  [`HeckeManuscriptMixedQuadratic1586PlusFieldBridge20260923.lean`](../../../UnitDistance/HeckeManuscriptMixedQuadratic1586PlusFieldBridge20260923.lean)
  defines the intended plus-radicand extension `B(√η)` and contains theorem
  declarations/proofs for its relative degree and quadratic prime-fiber Euler
  denominator (lines 24–52); compilation is pending, so these are not yet
  checked results. Its module header (lines 5–10) explicitly says it does not
  identify this quotient with the H6 rational-prime row or prove that row’s
  all-`n` coefficient majorant. The source does not state a plus-field theta
  reflection, completed FE, or strip estimate.
* [`HeckeManuscriptMixedQuadratic1586.lean`](../../../UnitDistance/HeckeManuscriptMixedQuadratic1586.lean)
  and its coefficient/Mellin leaves prove a source-defined quotient and its
  Dirichlet-series/Mellin normalization on the convergence half-plane. But
  the checked `FactorField` is the `D=−1` field, conductor 15015: see
  [`HeckeManuscriptMixedQuadratic1586ArithmeticRun20260920.lean`](../../../UnitDistance/HeckeManuscriptMixedQuadratic1586ArithmeticRun20260920.lean),
  lines 38–43, 128–133. Its Mellin leaf explicitly says it does not prove
  theta reflection/FE:
  [`HeckeManuscriptMixedQuadratic1586MellinRun20260920.lean`](../../../UnitDistance/HeckeManuscriptMixedQuadratic1586MellinRun20260920.lean),
  lines 8–18. These checked results do not transfer to the distinct `D=+1`,
  conductor-240240 row without a field/character and coefficient identity.
* The nearby `Mixed1586JacobiThetaReflectionRun20260920b.lean` and
  `Mixed1586JacobiFEPairRun20260920b.lean` prove a reflection and an entire
  functional-equation pair for a primitive conductor-429 principal-residue
  Dirichlet character. The FE module says explicitly at lines 8–15 that this
  is only the principal-residue restriction, not the full Hecke series over
  both ideal classes. Nor does this establish the plus-field row identity or
  its vertical growth.
* The general AINTLIB files do contain real analytic control for each
  individual Dedekind zeta: `AnalyticControl.lean` proves a polynomial
  vertical-strip bound for the pole-cleared completed zeta
  (`exists_completedDedekindZetaEntire_strip_bound`, lines 128–135) and a
  completed-zeta FE (`completedDedekindZetaEntire_one_sub`, lines 573–601).
  `RelativeHeckeCompletion.lean` makes the key limitation explicit in its
  header (lines 13–17): the quotient of the two entire completed zetas is
  meromorphic, and cancellation of nontrivial denominator zeros is a
  separate Hecke theorem. It proves the quotient FE as a meromorphic identity
  and identifies the quotient with a relative zeta quotient for `Re(s)>1`
  (lines 144–184); it does not make that relative quotient entire or provide
  its vertical-strip bound. Bounds on numerator and denominator separately
  cannot be divided to get polynomial growth without a denominator lower
  bound or a separate entire Hecke-factor theorem.

## Minimal next source theorem

The narrow missing theorem is not merely a fixed-field Dedekind-zeta FE. It
must identify the H6 `+1` rational row with the actual plus extension/Hecke
character and then supply the row’s analytic completion. A useful interface
would package:

* an exact coefficient/Euler identity `L₊ = ζ_{B(√η)}/ζ_B` on `Re(s)>1`
  (with the bad-factor convention used by the numeric replay);
* the all-`n` degree-two coefficient majorant;
* an entire (or appropriately pole-controlled) completion with the exact
  conductor 240240, gamma `[0,1]`, and conjugation-compatible root number
  `+1` FE;
* polynomial vertical-strip growth for the uncompleted `L₊` on the contour
  slab (or a proved theta/Mellin contour-decay theorem).

Those hypotheses imply the displayed expint AFE by the contour shift. The
staged plus-field Euler bridge, if compiled, supplies only the field and local
Euler-factor part. The `D=−1` FE/Mellin chain and AINTLIB fixed-field zeta
control provide useful ingredients, but neither closes the plus-row
identification or its relative-factor analyticity/growth.

## Algebraic consistency check for the plus radicand

Let `B=Q(√−35)` and `η=17+2√−35`, as in the plus-field bridge. If
`α²=η`, then
`α⁴−34α²+429=0`: the coefficient `34` is `Tr_B/Q(η)` and `429` is
`Norm_B/Q(η)` (the latter is proved in
[`HeckeManuscriptMixedQuadratic1586ArithmeticRun20260920.lean`](../../../UnitDistance/HeckeManuscriptMixedQuadratic1586ArithmeticRun20260920.lean),
lines 38–55). The staged plus bridge has a norm argument for `η` being
nonsquare in `B` at
[`HeckeManuscriptMixedQuadratic1586PlusFieldBridge20260923.lean`](../../../UnitDistance/HeckeManuscriptMixedQuadratic1586PlusFieldBridge20260923.lean),
lines 24–40, but that proof is uncompiled. Conditional on nonsquareness,
`B(α)` has degree four over `Q`; moreover
`√−35=(α²−17)/2`, so this quartic is the minimal polynomial of `α`.

For `f(X)=X⁴−34X²+429`, the quartic discriminant formula gives
`disc(f)=16·429·(34²−4·429)²=2,152,550,400`. The pinned H6 arithmetic
receipt records for mask 1586, twist `+1`, conductor 240240, gamma `[0,1]`,
and root number `+1` (the target-sigma row is also described at
[`h6-target-sigma-expint-plan.md`](h6-target-sigma-expint-plan.md), lines
5–7, 39–47). If this conductor is the Artin conductor/discriminant ratio
`|D_F|/|D_B|`, then `|D_B|=35` gives the expected
`|D_F|=35·240240=8,408,400`; the polynomial order index must therefore be
`sqrt(disc(f)/|D_F|)=16`. Equivalently, the expected relative discriminant
norm is `240240/35=6,864=16·429`. This is arithmetically consistent with
the receipt, but the receipt does not by itself prove that conductor
identification.

The archimedean data are consistent as well: `B` has signature `(0,1)`;
`F=B(α)` contains the imaginary quadratic field `B`, has degree four, and
therefore has signature `(0,2)`. The quotient of their Dedekind gamma factors
is one `Γ_C(s)=Γ_R(s)Γ_R(s+1)` factor, i.e. degree-two signature `[0,1]`.
Using this as the row gamma signature still requires identifying the H6
representation with that zeta quotient.

The precise unproved algebraic step exposed by the polynomial calculation is
the plus field's index/discriminant computation: prove
`[𝓞_F : Z[α]]=16` (or compute the relative different norm directly as 6864),
including the local contribution at 2. The existing exact discriminant
module `Mixed1586DiscriminantRun20260920.lean`, lines 33–106, computes the
different field, twist `−1` polynomial/order, and index one; it is not a
proof of this plus-field index. No compiled plus-field theorem currently
establishes the required index, Artin conductor ratio, or the row's FE/AFE.

## Additional check of existing relative-Hecke continuation route

The repository has an abstract, checked route that can construct an entire
relative factor from an actual signed-theta completion and a real-ray Euler
identity. `HeckeRealRayFactor.exists_entire_relative_factor_of_finite_euler_denominator_real`
requires a differentiable comparison completion and an identity of completed
products for every real `x>1`; `HeckeQuadraticContinuation.lean:46–60`
specializes that route to `heckeSignedCompletion`. It then gives an entire
relative factor and, via `RelativeEntireContinuation.entireRelativeFactor_one_sub`,
the inherited FE. This is not a ready-made theorem for the `+1` H6 quotient:
the specialized route also requires `r²=7` in the lower field, a positive
number of real places in that field, and the displayed real-ray zeta identity.
For this task the lower field is `B=Q(√−35)`, so `nrRealPlaces B=0`, contrary
to its `hFreal` premise; the plus bridge supplies no such signed theta or
real-ray identity. (See `HeckeQuadraticContinuation.lean:44–81` and
`HeckeSignedEntire.lean:79–96`.)

Thus existing analytic results divide into three levels:

1. **Checked individual-field facts:** AINTLIB proves entire pole-cleared
   completed Dedekind zeta, its `s↦1−s` symmetry, and polynomial strip bounds
   for that pole-cleared completion.
2. **Checked quotient facts:** `RelativeHeckeCompletion.lean:144–184` proves
   meromorphy and the symmetry of a quotient of two such completions, plus
   identification with the relative zeta quotient on `Re(s)>1`. This is a
   meromorphic FE for the quotient.
3. **Still needed for this AFE:** a holomorphic completed relative factor
   with the exact row normalization and a strip-growth bound for that factor.
   Dividing the two field-level bounds is invalid near denominator zeros;
   quotient symmetry does not remove those possible poles. A character-specific
   entire continuation/FE construction with a growth bound, or a directly
   matched theta reflection plus contour-decay proof, is still required.

No current source was found that instantiates the generic completed-zeta or
strong-Hecke-FE interfaces with the full `B(√η)/B` character and matches its
Euler coefficients, conductor 240240, gamma `[0,1]`, and root number `+1` to
the H6 row. This audit is source-only; it does not claim such an instantiation
is impossible.
