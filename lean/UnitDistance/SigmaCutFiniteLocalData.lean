module

public import UnitDistance.SigmaCutLocalFamily
public import UnitDistance.SigmaCutAbsoluteGenus
public import UnitDistance.SigmaDyadicInertiaCard

@[expose] public section
set_option backward.privateInPublic true


/-! Exact actual local image sizes at all eleven witness primes, uniformly
in every discrete arithmetic cut quotient retaining the actual field M. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP.SigmaCut
open ProCGroups.Presentations
variable (hgen : ArithmeticPresentation)
variable {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
  (q : ActualQuotient →ₜ* H) (r : H →* RetainedQuadratic.Q)
  (hr : r.comp q.toMonoidHom=(retained actualExtra).toMonoidHom)

def selectedDecompositionMap (a : Fin 11) :
    PrimeCompletion.AbsoluteDecomposition (selectedPrime a) →ₜ* H :=
  (q.comp (arithmeticProjection actualExtra hgen)).comp
    (SigmaUnramified.decompositionMap (selectedPrime a))

def selectedInertiaMap (a : Fin 11) :
    PrimeCompletion.AbsoluteInertia (selectedPrime a) →* H :=
  (selectedDecompositionMap hgen q a).toMonoidHom.comp
    (PrimeCompletion.AbsoluteInertia (selectedPrime a)).subtype

private theorem extra_inertia_card (i : Fin 5) :
    Nat.card (((extraDecompositionMap hgen q i).toMonoidHom.comp
      (PrimeCompletion.AbsoluteInertia (ExtraPrime.prime i)).subtype).range)=1 := by
  have he : ((extraDecompositionMap hgen q i).toMonoidHom.comp
      (PrimeCompletion.AbsoluteInertia (ExtraPrime.prime i)).subtype).range=⊥ := by
    apply le_antisymm _ bot_le
    rintro _ ⟨x,rfl⟩
    exact extra_inertia_killed hgen q i x
  rw [he]
  exact Nat.card_unique

include r hr

/-- Literal selected-prime inertia sizes, with no local hypotheses. -/
theorem selected_inertia_cards (a : Fin 11) :
    Nat.card (selectedInertiaMap hgen q a).range=Witness.ramification a := by
  fin_cases a
  · exact dyadic_finite_inertia_card actualExtra hgen q.toMonoidHom r hr
  · exact (odd_local_image_cards actualExtra hgen q r hr 0).1
  · exact (odd_local_image_cards actualExtra hgen q r hr 1).1
  · exact (odd_local_image_cards actualExtra hgen q r hr 2).1
  · exact (odd_local_image_cards actualExtra hgen q r hr 3).1
  · exact (odd_local_image_cards actualExtra hgen q r hr 4).1
  · exact extra_inertia_card hgen q 0
  · exact extra_inertia_card hgen q 1
  · exact extra_inertia_card hgen q 2
  · exact extra_inertia_card hgen q 3
  · exact extra_inertia_card hgen q 4

/-- Literal selected-prime decomposition sizes, with no local hypotheses. -/
theorem selected_decomposition_cards (a : Fin 11) :
    Nat.card (selectedDecompositionMap hgen q a).toMonoidHom.range=
      Witness.ramification a*Witness.residueDegree a := by
  fin_cases a
  · exact dyadic_finite_decomposition_card actualExtra hgen q.toMonoidHom r hr
  · exact (odd_local_image_cards actualExtra hgen q r hr 0).2
  · exact (odd_local_image_cards actualExtra hgen q r hr 1).2
  · exact (odd_local_image_cards actualExtra hgen q r hr 2).2
  · exact (odd_local_image_cards actualExtra hgen q r hr 3).2
  · exact (odd_local_image_cards actualExtra hgen q r hr 4).2
  · exact extra_decomposition_card hgen q r hr 0
  · exact extra_decomposition_card hgen q r hr 1
  · exact extra_decomposition_card hgen q r hr 2
  · exact extra_decomposition_card hgen q r hr 3
  · exact extra_decomposition_card hgen q r hr 4

/-- The two literal local image sizes at each selected prime. -/
theorem selected_local_image_cards (a : Fin 11) :
    Nat.card (selectedInertiaMap hgen q a).range=Witness.ramification a ∧
      Nat.card (selectedDecompositionMap hgen q a).toMonoidHom.range=
        Witness.ramification a*Witness.residueDegree a :=
  ⟨selected_inertia_cards hgen q r hr a,selected_decomposition_cards hgen q r hr a⟩

end UnitDistance.ArithmeticProP.SigmaCut
