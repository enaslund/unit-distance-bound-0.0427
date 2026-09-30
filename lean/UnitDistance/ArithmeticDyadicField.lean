module

public import UnitDistance.RationalGaloisBaseChange
public import UnitDistance.PadicTwoSquareclassIndependence
public import UnitDistance.QuadraticRootCharacterSurjectivity
public import UnitDistance.ArithmeticRetainedModel

@[expose] public section
set_option backward.privateInPublic true


/-! The actual retained field after base change to Q₂, and the actual
independent genus signs on its Galois group. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticDyadic
open ArithmeticChosenGenus ArithmeticRetained Multiquadratic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev LocalField := RationalGaloisBaseChange.Carrier RetainedField ℚ_[2]
def retainedEmbedding : RetainedField →ₐ[ℚ] LocalField :=
  RationalGaloisBaseChange.embedding RetainedField ℚ_[2]
def restriction : Gal(LocalField/ℚ_[2]) →* Gal(RetainedField/ℚ) :=
  RationalGaloisBaseChange.restriction RetainedField ℚ_[2]

def model : Gal(LocalField/ℚ_[2]) →* RetainedQuadratic.Q :=
  retainedModelEquiv.symm.toMonoidHom.comp restriction

theorem model_injective : Function.Injective model :=
  retainedModelEquiv.symm.injective.comp (RationalGaloisBaseChange.restriction_injective RetainedField ℚ_[2])

theorem model_base (σ : Gal(LocalField/ℚ_[2])) : (model σ).base=genusVector (restriction σ) := by
  have h := genusVector_retainedModelHom (retainedModelEquiv.symm (restriction σ))
  change genusVector (retainedModelEquiv (retainedModelEquiv.symm (restriction σ)))=(model σ).base at h
  rw [retainedModelEquiv.apply_symm_apply] at h
  exact h.symm

def genusRoot (i : Fin 7) : LocalField :=
  retainedEmbedding (algebraMap GenusField RetainedField (roots i))

theorem genusRoot_sq (i : Fin 7) : (genusRoot i)^2=(radicands i : LocalField) := by
  rw [genusRoot,← map_pow,← map_pow,roots_sq,map_ratCast,map_ratCast]

theorem genusRoot_ne_zero (i : Fin 7) : genusRoot i≠0 :=
  (map_ne_zero retainedEmbedding).mpr ((map_ne_zero (algebraMap GenusField RetainedField)).mpr (roots_ne_zero i))

theorem genusRoot_action (σ : Gal(LocalField/ℚ_[2])) (i : Fin 7) :
    σ (genusRoot i)=binarySign ((model σ).base i)*genusRoot i := by
  calc
    σ (genusRoot i)=retainedEmbedding ((restriction σ)
        (algebraMap GenusField RetainedField (roots i))) :=
      (RationalGaloisBaseChange.restriction_commutes RetainedField ℚ_[2] σ
        (algebraMap GenusField RetainedField (roots i))).symm
    _ = binarySign ((model σ).base i)*genusRoot i := by
      rw [restrict_genusVector,signAutomorphism_roots,map_mul,map_mul]
      simp only [binarySign,map_intCast,← model_base]
      rfl

def independentIndex : Fin 3 → Fin 7 := ![0,1,3]

/-- Actual three independent local signs, read from the true retained Galois action. -/
def signMap : Gal(LocalField/ℚ_[2]) →* Multiplicative (Fin 3 → ZMod 2) where
  toFun σ := Multiplicative.ofAdd (fun i => (model σ).base (independentIndex i))
  map_one' := by apply Multiplicative.toAdd.injective; funext i; simp
  map_mul' σ τ := by apply Multiplicative.toAdd.injective; funext i; simp

/-- All eight local genus sign vectors occur in the actual Q₂ Galois group. -/
theorem signMap_surjective : Function.Surjective signMap := by
  apply signHom_surjective_of_products
    (fun i => genusRoot (independentIndex i))
    (fun i => (PadicTwo.independentRadicand i : ℚ_[2]))
  · intro i
    have hv : ∀ i : Fin 3,radicands (independentIndex i)=(PadicTwo.independentRadicand i : ℚ) := by decide +kernel
    rw [genusRoot_sq,hv,map_intCast,Rat.cast_intCast]
  · intro σ i
    exact genusRoot_action σ (independentIndex i)
  · exact PadicTwo.independent_products

end UnitDistance.ArithmeticDyadic
