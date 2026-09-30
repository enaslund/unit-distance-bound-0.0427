module

public import UnitDistance.SigmaGenusGenerators
public import UnitDistance.GaloisEmbeddingRestriction
public import UnitDistance.ArithmeticRetainedModelChoice
public import UnitDistance.RetainedQuadraticTopology

@[expose] public section
set_option backward.privateInPublic true


/-! The actual global Galois group maps onto the actual retained field and
its concrete quadratic group model, with all seven generators aligned. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace UnitDistance.ArithmeticProP
open ArithmeticChosenGenus ArithmeticRetained ArithmeticGenusFrattini

private instance genusGalCommutative : IsMulCommutative Gal(GenusField/ℚ) := by
  refine ⟨⟨fun a b ↦ ?_⟩⟩
  apply genusGaloisEquiv.symm.injective
  rw [map_mul, map_mul, mul_comm]

def sigmaRetainedRestriction : Gal(maximalSigmaProTwo/ℚ) →ₜ* Gal(RetainedField/ℚ) :=
  GaloisEmbedding.restriction retainedFieldEmbeddingMaximalSigmaProTwo

theorem sigmaRetainedRestriction_surjective : Function.Surjective sigmaRetainedRestriction :=
  GaloisEmbedding.restriction_surjective retainedFieldEmbeddingMaximalSigmaProTwo

theorem sigmaRetainedRestriction_genus (σ : Gal(maximalSigmaProTwo/ℚ)) :
    genusVector (sigmaRetainedRestriction σ) = (sigmaGenusRestriction σ).toAdd := by
  let b : GenusField →ₐ[ℚ] RetainedField := IsScalarTower.toAlgHom ℚ GenusField RetainedField
  let e : GenusField →ₐ[ℚ] maximalSigmaProTwo :=
    genusInMaximal.val.comp genusInMaximalEquiv.symm.toAlgHom
  have hbase : GaloisEmbedding.restriction b (sigmaRetainedRestriction σ) =
      (sigmaRetainedRestriction σ).restrictNormal GenusField := by
    apply GaloisEmbedding.restriction_unique
    intro x
    exact AlgEquiv.restrictNormal_commutes (sigmaRetainedRestriction σ) GenusField x
  change (genusGaloisEquiv.symm
    ((sigmaRetainedRestriction σ).restrictNormal GenusField)).toAdd = _
  rw [← hbase]
  change (genusGaloisEquiv.symm (GaloisEmbedding.restriction b
    (GaloisEmbedding.restriction retainedFieldEmbeddingMaximalSigmaProTwo σ))).toAdd = _
  rw [← GaloisEmbedding.restriction_comp,
    GaloisEmbedding.restriction_independent
      (retainedFieldEmbeddingMaximalSigmaProTwo.comp b) e σ]
  rw [GaloisEmbedding.restriction_subfield]
  rfl

def sigmaRetainedGenerator (i : Fin 7) : Gal(RetainedField/ℚ) :=
  sigmaRetainedRestriction (sigmaGenerator i)

theorem sigmaRetainedGenerator_genus (i : Fin 7) :
    genusVector (sigmaRetainedGenerator i) = Pi.single i 1 := by
  rw [sigmaRetainedGenerator, sigmaRetainedRestriction_genus, sigmaGenerator_genus]
  rfl

/-- The retained model is aligned with the actual chosen arithmetic generators. -/
def sigmaRetainedModelEquiv : RetainedQuadratic.Q ≃* Gal(RetainedField/ℚ) :=
  retainedModelEquivOfLifts sigmaRetainedGenerator sigmaRetainedGenerator_genus

def sigmaRetainedModelMap : Gal(maximalSigmaProTwo/ℚ) →ₜ* RetainedQuadratic.Q where
  toMonoidHom := sigmaRetainedModelEquiv.symm.toMonoidHom.comp
    sigmaRetainedRestriction.toMonoidHom
  continuous_toFun := (continuous_of_discreteTopology : Continuous
    sigmaRetainedModelEquiv.symm).comp sigmaRetainedRestriction.continuous_toFun

theorem sigmaRetainedModelMap_surjective : Function.Surjective sigmaRetainedModelMap :=
  sigmaRetainedModelEquiv.symm.surjective.comp sigmaRetainedRestriction_surjective

theorem sigmaRetainedModelMap_generator (i : Fin 7) :
    sigmaRetainedModelMap (sigmaGenerator i) = RetainedQuadratic.Universal.basis i := by
  apply sigmaRetainedModelEquiv.injective
  change sigmaRetainedModelEquiv (sigmaRetainedModelEquiv.symm (sigmaRetainedGenerator i)) = _
  rw [sigmaRetainedModelEquiv.apply_symm_apply]
  exact (retainedModelEquivOfLifts_basis sigmaRetainedGenerator sigmaRetainedGenerator_genus i).symm

end UnitDistance.ArithmeticProP
