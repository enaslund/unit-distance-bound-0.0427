module

public import UnitDistance.MaximalSigmaH2Reduction
public import UnitDistance.RationalFiniteFieldUnitsH2
public import UnitDistance.ProTwoH2AbsoluteKernel

@[expose] public section
set_option backward.privateInPublic true


/-! The sharp actual H² bound for the maximal rational pro-two extension
unramified outside the six specified finite primes. The global norm and arithmetic kernel statements are proved dependencies. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.Cohomology

/-- The actual maximal pro-two Galois group has finite continuous H² of
dimension at most six. No local detection, relation-rank, or cohomological
finiteness premise is supplied to this endpoint. -/
theorem maximalSigmaProTwoH2_finiteDimensional_finrank_le :
    FiniteDimensional (ZMod 2)
      (continuousCohomologyZModPLifted 2
        (maximalProPOutside 2 sigmaPrimeSupport ≃ₐ[ℚ]
          maximalProPOutside 2 sigmaPrimeSupport) 2) ∧
    Module.finrank (ZMod 2)
      (continuousCohomologyZModPLifted 2
        (maximalProPOutside 2 sigmaPrimeSupport ≃ₐ[ℚ]
          maximalProPOutside 2 sigmaPrimeSupport) 2) ≤ 6 := by
  apply maximalSigmaProTwoH2_finiteDimensional_finrank_le_of_finite_inputs
    imaginaryFieldUnitsFiniteDetection
  intro U hmu
  apply finiteKummerContinuousH2Map_ker_le_proPStageInflation_ker sigmaPrimeSupport
    (hmu := hmu) (U := U)
  let e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  change (e (e.symm (⟨3, Nat.prime_three⟩ : Nat.Primes)) : ℕ) ∈
    sigmaRationalPrimes
  have he : e (e.symm (⟨3, Nat.prime_three⟩ : Nat.Primes)) =
      (⟨3, Nat.prime_three⟩ : Nat.Primes) := e.apply_symm_apply _
  rw [he]
  decide

end UnitDistance.ArithmeticProP
