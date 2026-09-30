module

public import UnitDistance.TensorEnergy
public import UnitDistance.StudentMoments
public import UnitDistance.TensorProfiles

@[expose] public section
set_option backward.privateInPublic true


/-!
# Ordinary endpoint coordinates and product overlap laws

Regroup logarithmic displacements together with their corresponding Student
positions. This is an actual ordinary-volume equivalence. The two elementary
measure lemmas transport overlap laws and factor two independent densities.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace UnitDistance

/-- Transport the actual overlap density through a measure-preserving
coordinate equivalence. -/
theorem overlapLaw_measurePreserving_coordinates {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] (m : Measure Ω) (n : Measure Ξ)
    (e : Ω ≃ᵐ Ξ) (he : MeasurePreserving e m n) (X Y : Ξ → ℝ) (Z : ℝ) :
    MeasurePreserving e (overlapLaw m (fun x => X (e x)) (fun x => Y (e x)) Z)
      (overlapLaw n X Y Z) := by
  refine ⟨e.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply e.measurable hs]
  simp only [overlapLaw, withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  exact he.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun x => ENNReal.ofReal (Real.exp (-(X x+Y x))/Z)) s

/-- Two independent endpoint blocks have exactly the product overlap law. -/
theorem prod_overlapLaw {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (m : Measure Ω) (n : Measure Ξ) [SFinite m] [SFinite n]
    (X Y : Ω → ℝ) (U V : Ξ → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hU : Measurable U) (hV : Measurable V) (Z W : ℝ) (hZ : 0 < Z) (_hW : 0 < W) :
    overlapLaw (m.prod n) (fun x => X x.1+U x.2) (fun x => Y x.1+V x.2) (Z*W) =
      (overlapLaw m X Y Z).prod (overlapLaw n U V W) := by
  unfold overlapLaw
  rw [prod_withDensity (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_mul_div_comm, ← Real.exp_add]
  congr 2
  ring

namespace Witness

variable {β γ : Type*} [Fintype β] [Fintype γ]

abbrev TensorEndpointCoordinates (β γ : Type*) := (β → ℂ) × (γ → ℝ × (ℂ × ℂ))

/-- Regroup each logarithmic displacement with its actual pair position. -/
def tensorOverlapCoordinates :
    ((γ → ℝ) × TensorCoordinates β γ) ≃ᵐ TensorEndpointCoordinates β γ :=
  ((MeasurableEquiv.prodAssoc.symm.trans
    (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl (γ → ℂ × ℂ)))).trans
      MeasurableEquiv.prodAssoc).trans
        ((MeasurableEquiv.refl (β → ℂ)).prodCongr
          (MeasurableEquiv.arrowProdEquivProdArrow ℝ (ℂ × ℂ) γ).symm)

omit [Fintype β] [Fintype γ] in
@[simp] theorem tensorOverlapCoordinates_apply (w : (γ → ℝ) × TensorCoordinates β γ) :
    tensorOverlapCoordinates w = (w.2.1, fun j => (w.1 j, w.2.2 j)) := rfl

theorem tensorOverlapCoordinates_measurePreserving :
    MeasurePreserving (tensorOverlapCoordinates (β := β) (γ := γ)) volume volume := by
  have h₁ : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : ((γ → ℝ) × ((β → ℂ) × (γ → ℂ × ℂ))) ≃ᵐ
        (((γ → ℝ) × (β → ℂ)) × (γ → ℂ × ℂ))) volume volume :=
    volume_preserving_prodAssoc.symm _
  have h₂ : MeasurePreserving
      (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl (γ → ℂ × ℂ)) :
        (((γ → ℝ) × (β → ℂ)) × (γ → ℂ × ℂ)) ≃ᵐ
          (((β → ℂ) × (γ → ℝ)) × (γ → ℂ × ℂ))) volume volume :=
    (Measure.measurePreserving_swap (μ := volume) (ν := volume)).prod (MeasurePreserving.id volume)
  have h₃ : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (((β → ℂ) × (γ → ℝ)) × (γ → ℂ × ℂ)) ≃ᵐ
        ((β → ℂ) × ((γ → ℝ) × (γ → ℂ × ℂ)))) volume volume := volume_preserving_prodAssoc
  have h₄ : MeasurePreserving
      ((MeasurableEquiv.refl (β → ℂ)).prodCongr
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ (ℂ × ℂ) γ).symm) volume volume :=
    (MeasurePreserving.id volume).prod
      ((volume_measurePreserving_arrowProdEquivProdArrow ℝ (ℂ × ℂ) γ).symm _)
  exact h₄.comp (h₃.comp (h₂.comp h₁))

/-- The first endpoint energy after the actual regrouping. -/
def tensorFirstEnergy (w : TensorEndpointCoordinates β γ) : ℝ :=
  (∑ i, compactEnergy (w.1 i)) + ∑ j, pairEnergy (w.2 j).2

/-- The second endpoint uses the literal normalized displacement. -/
def tensorSecondEnergy (w : TensorEndpointCoordinates β γ) : ℝ :=
  (∑ i, compactEnergy (w.1 i+1)) +
    ∑ j, pairEnergy ((w.2 j).2+reciprocalPairStep (w.2 j).1)

@[simp] theorem tensorFirstEnergy_coordinates (w : (γ → ℝ) × TensorCoordinates β γ) :
    tensorFirstEnergy (tensorOverlapCoordinates w) = firstEnergy tensorPositionEnergy w := rfl

@[simp] theorem tensorSecondEnergy_coordinates (w : (γ → ℝ) × TensorCoordinates β γ) :
    tensorSecondEnergy (tensorOverlapCoordinates w) = secondEnergy tensorPositionEnergy tensorStep w := rfl

theorem measurable_tensorFirstEnergy :
    Measurable (tensorFirstEnergy (β := β) (γ := γ)) := by
  have hc := continuous_compactEnergy.measurable
  have hp := measurable_pairEnergy
  unfold tensorFirstEnergy
  fun_prop

theorem measurable_tensorSecondEnergy :
    Measurable (tensorSecondEnergy (β := β) (γ := γ)) := by
  have hc := continuous_compactEnergy.measurable
  have hp := measurable_pairEnergy
  have hs := measurable_reciprocalPairStep
  unfold tensorSecondEnergy
  fun_prop

end Witness
end UnitDistance
