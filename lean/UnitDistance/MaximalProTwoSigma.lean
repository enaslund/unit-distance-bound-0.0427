module

public import UnitDistance.MaximalProPGroup
public import UnitDistance.SigmaPrimeSupport

@[expose] public section
set_option backward.privateInPublic true


/-! The actual maximal pro-two extension of Q with the six specified finite
ramification primes. Infinite places are unrestricted. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
namespace UnitDistance.ArithmeticProP

/-- The supremum of the actual finite Galois two-extensions with this support. -/
def maximalSigmaProTwo : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  maximalProPOutside 2 sigmaPrimeSupport

instance maximalSigmaProTwo_isGalois : IsGalois ℚ maximalSigmaProTwo :=
  maximalProPOutside_isGalois 2 sigmaPrimeSupport

/-- Every finite quotient in the actual open-normal basis is a two-group. -/
theorem maximalSigmaProTwo_hasPGroupOpenNormalBasis :
    ProCGroups.ProC.HasPGroupOpenNormalBasis 2
      (maximalSigmaProTwo ≃ₐ[ℚ] maximalSigmaProTwo) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact maximalProPOutside_galoisGroup_hasPGroupOpenNormalBasis 2 sigmaPrimeSupport

/-- The finite normal subextensions are precisely the actual admissible layers. -/
theorem finiteLayer_le_maximalSigmaProTwo_iff
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    E.toIntermediateField ≤ maximalSigmaProTwo ↔
      IsAdmissibleFiniteLayer 2 sigmaPrimeSupport E :=
  (isAdmissibleFiniteLayer_iff_le_maximalProPOutside 2 sigmaPrimeSupport E).symm

end UnitDistance.ArithmeticProP
