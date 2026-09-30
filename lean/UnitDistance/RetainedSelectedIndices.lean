module

public import UnitDistance.RetainedSelectedLocalData
public import UnitDistance.AbsolutePrimeIndices

@[expose] public section
set_option backward.privateInPublic true


/-! Actual selected-prime ramification and residue indices of the retained
number field, recovered from the proved absolute local image sizes. -/
noncomputable section
namespace UnitDistance.ArithmeticProP.SigmaCut
open NumberField ArithmeticRetained NumberFieldAnalysis
variable (hgen : ArithmeticPresentation)
include hgen

/-- The retained number field has exactly the witness's selected ramification indices. -/
theorem retained_selected_ramification (a : Fin 11) :
    (rationalPrimeIdeal (Witness.primes a)).ramificationIdxIn (𝓞 RetainedField)=
      Witness.ramification a := by
  have h := retained_selected_inertia_image_card hgen a
  rw [PrimeCompletion.inertiaRestriction_card] at h
  exact h

/-- The retained number field has exactly the witness's selected residue degrees. -/
theorem retained_selected_residue (a : Fin 11) :
    (rationalPrimeIdeal (Witness.primes a)).inertiaDegIn (𝓞 RetainedField)=
      Witness.residueDegree a := by
  exact (PrimeCompletion.ramification_residue_of_absolute_image_cards
    (selectedPrime a) RetainedField sigmaRetainedAbsoluteEmbedding
    (Witness.ramification a) (Witness.residueDegree a)
    (by fin_cases a <;> decide)
    (retained_selected_inertia_image_card hgen a)
    (retained_selected_decomposition_image_card hgen a)).2

end UnitDistance.ArithmeticProP.SigmaCut
