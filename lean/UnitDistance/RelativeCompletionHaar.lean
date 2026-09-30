module

public import UnitDistance.RelativeCompletionCoordinates
public import Mathlib.Topology.Algebra.GroupWithZero

@[expose] public section
set_option backward.privateInPublic true


/-! # Exact normalized Haar transport between actual partner completions -/

noncomputable section
open scoped NumberField nonZeroDivisors Classical Topology
open NumberField IsDedekindDomain WithZero MeasureTheory

namespace UnitDistance.RelativeCompletion

open Local.ValuedHaar

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

local instance transportMeasurableSpace (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance transportBorelSpace (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

/-- The completed involution as an additive homeomorphism. -/
def completionAddEquiv (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    v.adicCompletion K ≃ₜ+ w.adicCompletion K where
  toAddEquiv := (completionInvolution ι v w hw).toAddEquiv
  continuous_toFun := completionInvolution_continuous ι v w hw
  continuous_invFun := completionInvolution_symm_continuous ι v w hw

theorem completionAddEquiv_preimage_ball (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal)
    (a : ℤ) :
    completionAddEquiv ι v w hw ⁻¹' (ball (w.adicCompletion K) a : Set (w.adicCompletion K)) =
      (ball (v.adicCompletion K) a : Set (v.adicCompletion K)) := by
  ext x
  change intValuation (w.adicCompletion K) (completionInvolution ι v w hw x) ≤ WithZero.exp a ↔ _
  rw [completionInvolution_intValuation]
  rfl

/-- The actual involution transports normalized additive Haar exactly; no
scaling constant or measure-preservation hypothesis is supplied. -/
theorem completionInvolution_measurePreserving (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    MeasurePreserving (completionInvolution ι v w hw)
      (normalizedHaar (v.adicCompletion K)) (normalizedHaar (w.adicCompletion K)) := by
  let e := completionAddEquiv ι v w hw
  haveI : ((normalizedHaar (v.adicCompletion K)).map e).IsAddHaarMeasure := inferInstance
  have hm : (normalizedHaar (v.adicCompletion K)).map e (unitBall (w.adicCompletion K)) = 1 := by
    change ((normalizedHaar (v.adicCompletion K)).map e) (ball (w.adicCompletion K) 0 : Set _) = 1
    have he : Measurable (e : v.adicCompletion K → w.adicCompletion K) :=
      e.continuous_toFun.measurable
    rw [Measure.map_apply he (ball_clopen (w.adicCompletion K) 0).isOpen.measurableSet]
    change normalizedHaar (v.adicCompletion K) (completionAddEquiv ι v w hw ⁻¹'
      (ball (w.adicCompletion K) 0 : Set (w.adicCompletion K))) = 1
    rw [completionAddEquiv_preimage_ball]
    exact Measure.addHaarMeasure_self
  refine ⟨e.continuous_toFun.measurable, ?_⟩
  change (normalizedHaar (v.adicCompletion K)).map e = _
  rw [Measure.addHaarMeasure_unique ((normalizedHaar (v.adicCompletion K)).map e)
    (unitBall (w.adicCompletion K)), hm, one_smul]
  rfl

/-- The inverse transport also preserves normalized additive Haar exactly. -/
theorem completionInvolution_symm_measurePreserving (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    MeasurePreserving (completionInvolution ι v w hw).symm
      (normalizedHaar (w.adicCompletion K)) (normalizedHaar (v.adicCompletion K)) :=
  MeasurePreserving.symm (completionHomeomorph ι v w hw).toMeasurableEquiv
    (completionInvolution_measurePreserving ι v w hw)

/-- The actual two-completion coordinate identification preserves the actual
product of normalized additive Haar measures. -/
theorem pairCoordinates_measurePreserving (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    MeasurePreserving (pairCoordinates ι v w hw)
      ((normalizedHaar (v.adicCompletion K)).prod (normalizedHaar (w.adicCompletion K)))
      ((normalizedHaar (v.adicCompletion K)).prod (normalizedHaar (v.adicCompletion K))) :=
  (MeasurePreserving.id (normalizedHaar (v.adicCompletion K))).prod
    (completionInvolution_symm_measurePreserving ι v w hw)

/-- The common actual local field has the base-prime residue cardinality
when the original pair is an actual split pair. -/
theorem commonCompletion_residueCard {S : Type*} [Fintype S] (ι : K ≃ₐ[F] K)
    (D : RelativeIdealCosets.SplitPrimeFamily ι S) (s : S) :
    residueCard ((D.prime (s, false)).adicCompletion K) = Ideal.absNorm (D.basePrime s).asIdeal := by
  rw [Local.AdicResidue.residueCard_eq_absNorm, RelativeIdealCosets.splitPrime_absNorm]

end UnitDistance.RelativeCompletion
