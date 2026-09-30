module

public import UnitDistance.RelativeCompletionEquiv
public import UnitDistance.LocalSplitSteps

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual paired completion coordinates for relative norm-one elements -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical Topology
open NumberField IsDedekindDomain WithZero

namespace UnitDistance.RelativeCompletion

open Local.ValuedHaar

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

local instance coordinatesMeasurableSpace (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance coordinatesBorelSpace (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

/-- Both coordinates are placed in the first actual K-prime completion by
transporting the partner along the actual involution. -/
def pairCoordinates (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    v.adicCompletion K × w.adicCompletion K ≃+* v.adicCompletion K × v.adicCompletion K :=
  RingEquiv.prodCongr (RingEquiv.refl _) (completionInvolution ι v w hw).symm

/-- Actual diagonal field coordinates become (β, ιβ) in the common completion. -/
theorem pairCoordinates_field (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal)
    (β : K) :
    pairCoordinates ι v w hw (algebraMap K (v.adicCompletion K) β,
      algebraMap K (w.adicCompletion K) β) =
        (algebraMap K (v.adicCompletion K) β, algebraMap K (v.adicCompletion K) (ι β)) := by
  refine Prod.ext (by rfl) ?_
  change (completionInvolution ι v w hw).symm (algebraMap K (w.adicCompletion K) β) = _
  apply (completionInvolution ι v w hw).injective
  rw [RingEquiv.apply_symm_apply, completionInvolution_field,
    RelativeUnits.quadratic_automorphism_involutive ι hι]

/-- Actual field norm one produces a reciprocal pair in the common completion. -/
theorem pairCoordinates_normOne (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal)
    (β : K) (hβ : Algebra.norm F β = 1) :
    pairCoordinates ι v w hw (algebraMap K (v.adicCompletion K) β,
      algebraMap K (w.adicCompletion K) β) =
        (algebraMap K (v.adicCompletion K) β, (algebraMap K (v.adicCompletion K) β)⁻¹) := by
  have hn : β * ι β = 1 := by
    rw [← RelativeUnits.norm_eq_mul_involution ι hι, hβ, map_one]
  have hb : β ≠ 0 := by intro h; simpa [h] using hn
  have hi : ι β = β⁻¹ := by
    apply mul_left_cancel₀ hb
    rw [hn, mul_inv_cancel₀ hb]
  rw [pairCoordinates_field ι hι, hi, map_inv₀]

/-- The signed valuation label is exactly the exponent in the actual
uniformizer-and-unit reciprocal-step model. -/
theorem normOne_eq_reciprocalStep_of_valuation (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal)
    (β : K) (hβ : Algebra.norm F β = 1) (n : ℤ)
    (hv : v.valuation K β = WithZero.exp (-n)) :
    ∃ u : ValuationOneUnits (v.adicCompletion K),
      pairCoordinates ι v w hw (algebraMap K (v.adicCompletion K) β,
        algebraMap K (w.adicCompletion K) β) = (reciprocalSteps (v.adicCompletion K)).step n u := by
  let t : v.adicCompletion K := algebraMap K (v.adicCompletion K) β
  have ht : intValuation (v.adicCompletion K) t = WithZero.exp (-n) := by
    rw [SIntegerCRT.canonical_intValuation_eq, SIntegerCRT.valued_field, hv]
  let u : ValuationOneUnits (v.adicCompletion K) :=
    ⟨uniformizer (v.adicCompletion K) ^ (-n) * t, by
      rw [map_mul, intValuation_uniformizer_zpow, ht, neg_neg, ← WithZero.exp_add,
        add_neg_cancel, WithZero.exp_zero]⟩
  have hu : uniformizer (v.adicCompletion K) ^ n * (u : v.adicCompletion K) = t := by
    change uniformizer (v.adicCompletion K) ^ n *
      (uniformizer (v.adicCompletion K) ^ (-n) * t) = t
    rw [← mul_assoc, ← zpow_add₀ (uniformizer_ne_zero _), add_neg_cancel, zpow_zero, one_mul]
  refine ⟨u, ?_⟩
  rw [pairCoordinates_normOne ι hι v w hw β hβ]
  apply Prod.ext hu.symm
  change t⁻¹ = uniformizer (v.adicCompletion K) ^ (-n) * (u : v.adicCompletion K)⁻¹
  rw [← hu, mul_inv, ← zpow_neg]

end UnitDistance.RelativeCompletion
