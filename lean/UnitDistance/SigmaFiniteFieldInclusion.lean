module

public import UnitDistance.MaximalProTwoSigma
public import UnitDistance.FiniteFieldImage
public import UnitDistance.SigmaRamification
public import UnitDistance.ArithmeticCatalogRamification

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite catalog fields embed in the actual maximal pro-2 extension
with finite ramification supported on the six manuscript primes. -/
noncomputable section
open NumberField
namespace UnitDistance.ArithmeticProP
open QuadraticRamification
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

/-- An actual finite Galois2-extension unramified outsideΣ is a finite layer
of the constructed maximal extension. -/
theorem finiteGaloisImage_le_maximalSigmaProTwo
    (hp : IsPGroup 2 (K ≃ₐ[ℚ] K)) (hu : UnramifiedAway K 30030) :
    (finiteGaloisImage K).toIntermediateField ≤ maximalSigmaProTwo := by
  apply (finiteLayer_le_maximalSigmaProTwo_iff (finiteGaloisImage K)).mpr
  exact ⟨finiteGaloisImage_isPGroup K hp,
    unramifiedOutsideSigma_of_unramifiedAway (finiteGaloisImage K)
      (finiteGaloisImage_unramifiedAway K hu)⟩

/-- The inclusion gives an actual algebra embedding of the original field. -/
def embeddingMaximalSigmaProTwo
    (hp : IsPGroup 2 (K ≃ₐ[ℚ] K)) (hu : UnramifiedAway K 30030) :
    K →ₐ[ℚ] maximalSigmaProTwo :=
  (IntermediateField.inclusion (finiteGaloisImage_le_maximalSigmaProTwo K hp hu)).comp
    (finiteGaloisImageEquiv K).toAlgHom

/-- The concrete retained field's actual Galois group is a2-group. -/
theorem retainedField_isPGroup :
    IsPGroup 2 (ArithmeticRetained.RetainedField ≃ₐ[ℚ] ArithmeticRetained.RetainedField) := by
  apply IsPGroup.of_card (n := 19)
  rw [ArithmeticRetained.retainedField_galoisGroup_card]
  norm_num

/-- The manuscript's concrete degree2^19 field embeds in the actual maximal
pro-2 extension unramified outsideΣ. -/
def retainedFieldEmbeddingMaximalSigmaProTwo :
    ArithmeticRetained.RetainedField →ₐ[ℚ] maximalSigmaProTwo :=
  embeddingMaximalSigmaProTwo ArithmeticRetained.RetainedField retainedField_isPGroup
    ArithmeticRetained.retainedField_unramifiedAway

/-- The retained field's literal image is a subfield of that extension. -/
theorem retainedFieldImage_le_maximalSigmaProTwo :
    (finiteGaloisImage ArithmeticRetained.RetainedField).toIntermediateField ≤
      maximalSigmaProTwo :=
  finiteGaloisImage_le_maximalSigmaProTwo ArithmeticRetained.RetainedField
    retainedField_isPGroup ArithmeticRetained.retainedField_unramifiedAway

end UnitDistance.ArithmeticProP
