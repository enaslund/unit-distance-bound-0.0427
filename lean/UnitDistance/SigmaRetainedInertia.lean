module

public import UnitDistance.SigmaRetainedProjection
public import UnitDistance.SigmaUnramifiedFrobenius
public import UnitDistance.RationalInertiaBaseChange

@[expose] public section
set_option backward.privateInPublic true


/-! The actual retained-model inertia image is the finite Galois restriction
image of the retained arithmetic field, independent of model coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace UnitDistance.ArithmeticProP
open ArithmeticRetained

/-- The actual retained field inside the fixed rational algebraic closure. -/
def sigmaRetainedAbsoluteEmbedding : RetainedField →ₐ[ℚ] AlgebraicClosure ℚ :=
  maximalSigmaProTwo.val.comp retainedFieldEmbeddingMaximalSigmaProTwo

theorem sigmaRetainedRestriction_decomposition (p : Nat.Primes)
    (d : PrimeCompletion.AbsoluteDecomposition p) :
    sigmaRetainedRestriction (SigmaUnramified.decompositionMap p d)=
      PrimeCompletion.decompositionRestriction p RetainedField sigmaRetainedAbsoluteEmbedding d := by
  symm
  apply GaloisEmbedding.restriction_unique
  intro x
  change ((retainedFieldEmbeddingMaximalSigmaProTwo
    (sigmaRetainedRestriction (SigmaUnramified.decompositionMap p d) x) : maximalSigmaProTwo) :
      AlgebraicClosure ℚ)=d.val (sigmaRetainedAbsoluteEmbedding x)
  rw [sigmaRetainedRestriction,GaloisEmbedding.restriction_commutes]
  exact absoluteToMaximalProPOutside_apply 2 sigmaPrimeSupport d.val
    (retainedFieldEmbeddingMaximalSigmaProTwo x)

/-- Cardinalities of actual retained-model inertia are literal arithmetic
inertia image cardinalities. -/
theorem sigmaRetainedModel_inertia_card (p : Nat.Primes) :
    Nat.card (((sigmaRetainedModelMap.comp (SigmaUnramified.decompositionMap p)).toMonoidHom.comp
      (PrimeCompletion.AbsoluteInertia p).subtype).range)=
      Nat.card (PrimeCompletion.inertiaRestriction p RetainedField sigmaRetainedAbsoluteEmbedding).range := by
  have he : (sigmaRetainedModelMap.comp (SigmaUnramified.decompositionMap p)).toMonoidHom.comp
      (PrimeCompletion.AbsoluteInertia p).subtype=
      sigmaRetainedModelEquiv.symm.toMonoidHom.comp
        (PrimeCompletion.inertiaRestriction p RetainedField sigmaRetainedAbsoluteEmbedding) := by
    apply MonoidHom.ext
    intro σ
    change sigmaRetainedModelEquiv.symm (sigmaRetainedRestriction (SigmaUnramified.decompositionMap p σ.val))=_
    rw [sigmaRetainedRestriction_decomposition]
    rfl
  rw [he,MonoidHom.range_comp]
  exact Subgroup.card_map_of_injective sigmaRetainedModelEquiv.symm.injective

end UnitDistance.ArithmeticProP
