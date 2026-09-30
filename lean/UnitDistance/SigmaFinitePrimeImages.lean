module

public import UnitDistance.AbsolutePrimeImages
public import UnitDistance.SigmaUnramifiedFrobenius

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite-prime restriction diagrams for finite fields in the constructed
maximal arithmetic extension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP
open PrimeCompletion
variable (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
  (j : K →ₐ[ℚ] maximalSigmaProTwo)

def sigmaAbsoluteEmbedding : K →ₐ[ℚ] AlgebraicClosure ℚ := maximalSigmaProTwo.val.comp j

theorem sigmaRestriction_decomposition (p : Nat.Primes) (d : AbsoluteDecomposition p) :
    GaloisEmbedding.restriction j (SigmaUnramified.decompositionMap p d)=
      decompositionRestriction p K (sigmaAbsoluteEmbedding K j) d := by
  symm
  apply GaloisEmbedding.restriction_unique
  intro x
  change ((j (GaloisEmbedding.restriction j (SigmaUnramified.decompositionMap p d) x) :
    maximalSigmaProTwo) : AlgebraicClosure ℚ)=d.val (sigmaAbsoluteEmbedding K j x)
  rw [GaloisEmbedding.restriction_commutes]
  exact absoluteToMaximalProPOutside_apply 2 sigmaPrimeSupport d.val (j x)

theorem sigmaRestriction_inertia (p : Nat.Primes) (d : AbsoluteInertia p) :
    GaloisEmbedding.restriction j (SigmaUnramified.decompositionMap p d.val)=
      inertiaRestriction p K (sigmaAbsoluteEmbedding K j) d :=
  sigmaRestriction_decomposition K j p d.val

end UnitDistance.ArithmeticProP
