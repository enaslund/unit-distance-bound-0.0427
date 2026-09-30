module

public import UnitDistance.SigmaCutFiniteLocalData
public import UnitDistance.SigmaRetainedInertia

@[expose] public section
set_option backward.privateInPublic true


/-! Selected actual local image sizes in the independently constructed
retained number field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP.SigmaCut
open ArithmeticRetained
variable (hgen : ArithmeticPresentation)
include hgen

theorem retained_selected_inertia_image_card (a : Fin 11) :
    Nat.card (PrimeCompletion.inertiaRestriction (selectedPrime a) RetainedField
      sigmaRetainedAbsoluteEmbedding).range=Witness.ramification a := by
  have h := selected_inertia_cards hgen (retained actualExtra) (MonoidHom.id _)
    (by rfl) a
  have he : selectedInertiaMap hgen (retained actualExtra) a=
      (sigmaRetainedModelMap.comp (SigmaUnramified.decompositionMap (selectedPrime a))).toMonoidHom.comp
        (PrimeCompletion.AbsoluteInertia (selectedPrime a)).subtype := by
    apply MonoidHom.ext
    intro σ
    exact retained_arithmeticProjection actualExtra hgen
      (SigmaUnramified.decompositionMap (selectedPrime a) σ.val)
  rw [he,sigmaRetainedModel_inertia_card] at h
  exact h

theorem retained_selected_decomposition_image_card (a : Fin 11) :
    Nat.card (PrimeCompletion.decompositionRestriction (selectedPrime a) RetainedField
      sigmaRetainedAbsoluteEmbedding).range=Witness.ramification a*Witness.residueDegree a := by
  have h := selected_decomposition_cards hgen (retained actualExtra) (MonoidHom.id _)
    (by rfl) a
  have he : (selectedDecompositionMap hgen (retained actualExtra) a).toMonoidHom=
      sigmaRetainedModelEquiv.symm.toMonoidHom.comp
        (PrimeCompletion.decompositionRestriction (selectedPrime a) RetainedField sigmaRetainedAbsoluteEmbedding) := by
    apply MonoidHom.ext
    intro σ
    change retained actualExtra (arithmeticProjection actualExtra hgen
      (SigmaUnramified.decompositionMap (selectedPrime a) σ))=_
    rw [retained_arithmeticProjection]
    exact congrArg sigmaRetainedModelEquiv.symm (sigmaRetainedRestriction_decomposition (selectedPrime a) σ)
  rw [he,MonoidHom.range_comp,
    Subgroup.card_map_of_injective sigmaRetainedModelEquiv.symm.injective] at h
  exact h

end UnitDistance.ArithmeticProP.SigmaCut
