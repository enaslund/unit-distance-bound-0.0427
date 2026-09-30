module

public import UnitDistance.SigmaFinitePrimeImages
public import UnitDistance.SigmaCutFiniteLocalData

@[expose] public section
set_option backward.privateInPublic true


/-! Actual restriction diagrams in each finite arithmetic cut layer retaining M. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP.SigmaCut
open PrimeCompletion NumberFieldAnalysis
variable (hgen : ArithmeticPresentation)
variable (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
  (j : K →ₐ[ℚ] maximalSigmaProTwo)
  (q : ActualQuotient →ₜ* Gal(K/ℚ)) (r : Gal(K/ℚ) →* RetainedQuadratic.Q)
  (hr : r.comp q.toMonoidHom=(retained actualExtra).toMonoidHom)
  (hq : ∀g : SigmaGroup, q (arithmeticProjection actualExtra hgen g)=GaloisEmbedding.restriction j g)

include hq in
theorem selectedDecompositionMap_eq_restriction (a : Fin 11) :
    (selectedDecompositionMap hgen q a).toMonoidHom=
      decompositionRestriction (selectedPrime a) K (sigmaAbsoluteEmbedding K j) := by
  apply MonoidHom.ext
  intro d
  change q (arithmeticProjection actualExtra hgen (SigmaUnramified.decompositionMap (selectedPrime a) d))=_
  rw [hq]
  exact sigmaRestriction_decomposition K j _ d

include hq in
theorem selectedInertiaMap_eq_restriction (a : Fin 11) :
    selectedInertiaMap hgen q a=
      inertiaRestriction (selectedPrime a) K (sigmaAbsoluteEmbedding K j) := by
  change (selectedDecompositionMap hgen q a).toMonoidHom.comp _=_
  rw [selectedDecompositionMap_eq_restriction hgen K j q hq]
  rfl

include hr hq in
theorem retained_restriction (g : SigmaGroup) :
    r (GaloisEmbedding.restriction j g)=sigmaRetainedModelMap g := by
  rw [←hq]
  exact (DFunLike.congr_fun hr (arithmeticProjection actualExtra hgen g)).trans
    (retained_arithmeticProjection actualExtra hgen g)

end UnitDistance.ArithmeticProP.SigmaCut
