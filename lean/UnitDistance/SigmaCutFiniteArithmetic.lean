module

public import UnitDistance.SigmaCutFiniteRestriction
public import UnitDistance.AbsolutePrimeIndices

@[expose] public section
set_option backward.privateInPublic true


/-! Actual ideal ramification and residue degrees in
every finite arithmetic cut layer retaining M. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField
namespace UnitDistance.ArithmeticProP.SigmaCut
open PrimeCompletion NumberFieldAnalysis
variable (hgen : ArithmeticPresentation)
variable (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
  (j : K →ₐ[ℚ] maximalSigmaProTwo)
  (q : ActualQuotient →ₜ* Gal(K/ℚ)) (r : Gal(K/ℚ) →* RetainedQuadratic.Q)
  (hr : r.comp q.toMonoidHom=(retained actualExtra).toMonoidHom)
  (hq : ∀g : SigmaGroup, q (arithmeticProjection actualExtra hgen g)=GaloisEmbedding.restriction j g)

include hr hq
/-- Both actual ideal indices at all eleven primes are the literal witness data. -/
theorem selected_ramification_residue (a : Fin 11) :
    (rationalPrimeIdeal (Witness.primes a)).ramificationIdxIn (𝓞 K)=Witness.ramification a ∧
    (rationalPrimeIdeal (Witness.primes a)).inertiaDegIn (𝓞 K)=Witness.residueDegree a := by
  have h := selected_local_image_cards hgen q r hr a
  rw [selectedInertiaMap_eq_restriction hgen K j q hq a,
    selectedDecompositionMap_eq_restriction hgen K j q hq a] at h
  exact ramification_residue_of_absolute_image_cards (p:=selectedPrime a) (M:=K)
    (j:=sigmaAbsoluteEmbedding K j) _ _ (by fin_cases a <;> decide) h.1 h.2

end UnitDistance.ArithmeticProP.SigmaCut
