module

public import UnitDistance.SigmaOddFiniteGeneration
public import UnitDistance.OddLocalRetainedImage

@[expose] public section
set_option backward.privateInPublic true


/-! Exact cardinalities of actual arithmetic odd inertia/decomposition images
in every discrete quotient retaining M and imposing the displayed cuts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP
variable {P : Type*} [Group P] [TopologicalSpace P] [DiscreteTopology P]
  (q : SigmaGroup →ₜ* P) (ρ : P →* RetainedQuadratic.Q)
  (hρ : ∀ g,ρ (q g)=sigmaRetainedModelMap g) (i : Fin 5)
include hρ

theorem sigmaOdd_inertia_base : (ρ (q (sigmaOddInertia i))).base=RetainedQuadratic.Cut.inertiaVector i := by
  rw [hρ,sigmaRetainedModelMap_base,sigmaOddInertia_genus]
  have h : ∀ i : Fin 5,UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)=
      RetainedQuadratic.Cut.inertiaVector i := by decide +kernel
  exact h i

theorem sigmaOdd_frobenius_base : (ρ (q (sigmaOddFrobenius i))).base=RetainedQuadratic.Cut.frobeniusVector i := by
  rw [hρ,sigmaRetainedModelMap_base,sigmaOddFrobenius_genus]
  have h : ∀ i : Fin 5,UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i)=
      RetainedQuadratic.Cut.frobeniusVector i := by decide +kernel
  exact h i

omit ρ hρ in
theorem sigmaOdd_image_commute (ht : q (sigmaOddInertia i)^2=1) :
    Commute (q (sigmaOddInertia i)) (q (sigmaOddFrobenius i)) := by
  have h := congrArg q (sigmaOdd_tame i)
  simp only [map_mul,map_inv,map_pow] at h
  have hm : UniversalQuadratic.oddPrimes i%2=1 := by fin_cases i <;> decide
  rw [pow_eq_pow_mod _ ht,hm,pow_one] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

include hρ in
theorem sigmaOdd_local_image_cards
    (ht : q (sigmaOddInertia i)^2=1)
    (hf : q (sigmaOddFrobenius i)^OddLocal.residueDegree i=1) :
    Nat.card ((q.comp (sigmaOddInertiaMap i)).toMonoidHom.range)=2 ∧
    Nat.card ((q.comp (sigmaOddDecompositionMap i)).toMonoidHom.range)=2*OddLocal.residueDegree i := by
  rw [sigmaOdd_inertia_range,sigmaOdd_decomposition_range]
  have hc := sigmaOdd_image_commute q i ht
  exact ⟨OddLocal.card_inertia_of_retained i _ _ ht hf hc ρ
      (sigmaOdd_inertia_base q ρ hρ i) (sigmaOdd_frobenius_base q ρ hρ i),
    OddLocal.card_decomposition_of_retained i _ _ ht hf hc ρ
      (sigmaOdd_inertia_base q ρ hρ i) (sigmaOdd_frobenius_base q ρ hρ i)⟩

end UnitDistance.ArithmeticProP
