module

public import UnitDistance.SigmaFreeSource
public import UnitDistance.SigmaRetainedProjection
public import UnitDistance.SigmaComplexConjugation

@[expose] public section
set_option backward.privateInPublic true


/-! The actual free arithmetic source maps onto the retained model, and an
actual lift of complex conjugation has the required elementary coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace UnitDistance.ArithmeticProP
open ArithmeticRetained

theorem sigmaRetainedModelMap_base (σ : Gal(maximalSigmaProTwo/ℚ)) :
    (sigmaRetainedModelMap σ).base = (sigmaGenusRestriction σ).toAdd := by
  have h := genusVector_retainedModelHomOfLifts sigmaRetainedGenerator
    sigmaRetainedGenerator_genus (sigmaRetainedModelMap σ)
  change genusVector (sigmaRetainedModelEquiv (sigmaRetainedModelMap σ)) =
    (sigmaRetainedModelMap σ).base at h
  have he : sigmaRetainedModelEquiv (sigmaRetainedModelMap σ) = sigmaRetainedRestriction σ :=
    sigmaRetainedModelEquiv.apply_symm_apply _
  rw [he] at h
  exact h.symm.trans (sigmaRetainedRestriction_genus σ)

def sigmaFreeRetainedMap : FiniteFreeProTwo.Carrier 7 →ₜ* RetainedQuadratic.Q :=
  sigmaRetainedModelMap.comp sigmaFreeMap

theorem sigmaFreeRetainedMap_surjective : Function.Surjective sigmaFreeRetainedMap :=
  sigmaRetainedModelMap_surjective.comp sigmaFreeMap_surjective

theorem sigmaFreeRetainedMap_generator (i : Fin 7) :
    sigmaFreeRetainedMap (FiniteFreeProTwo.generator 7 i) = RetainedQuadratic.Universal.basis i := by
  change sigmaRetainedModelMap (sigmaFreeMap (FiniteFreeProTwo.generator 7 i)) = _
  rw [sigmaFreeMap_generator, sigmaRetainedModelMap_generator]

theorem sigmaFreeRetainedMap_generator_base (i : Fin 7) :
    (sigmaFreeRetainedMap (FiniteFreeProTwo.generator 7 i)).base = Pi.single i 1 := by
  rw [sigmaFreeRetainedMap_generator]
  rfl

/-- An actual free-source preimage of the actual arithmetic complex conjugation. -/
def sigmaFreeConjugation : FiniteFreeProTwo.Carrier 7 :=
  Function.surjInv sigmaFreeMap_surjective sigmaComplexConjugation

theorem sigmaFreeConjugation_image :
    sigmaFreeMap sigmaFreeConjugation = sigmaComplexConjugation :=
  Function.surjInv_eq sigmaFreeMap_surjective sigmaComplexConjugation

theorem sigmaFreeConjugation_base :
    (sigmaFreeRetainedMap sigmaFreeConjugation).base = Pi.single 0 1 := by
  change (sigmaRetainedModelMap (sigmaFreeMap sigmaFreeConjugation)).base = _
  rw [sigmaFreeConjugation_image, sigmaRetainedModelMap_base, sigmaComplexConjugation_genus]
  rfl

/-- The infinity-square word lies in the actual arithmetic relation kernel. -/
theorem sigmaFreeConjugation_square_mem : sigmaFreeConjugation^2 ∈ sigmaRelationKernel := by
  change sigmaFreeMap (sigmaFreeConjugation^2) = 1
  rw [map_pow, sigmaFreeConjugation_image, sigmaComplexConjugation_square]

end UnitDistance.ArithmeticProP
