module

public import UnitDistance.ArithmeticDyadicField

@[expose] public section
set_option backward.privateInPublic true


/-! The four actual Q₂ squareclass relations determine all seven local
genus coordinates from the three independent coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticDyadic
open ArithmeticChosenGenus ArithmeticRetained ArithmeticCatalog Multiquadratic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def localMaskRoot (m : ℕ) : LocalField :=
  retainedEmbedding (algebraMap GenusField RetainedField (maskRoot m))

theorem localMaskRoot_sq (m : ℕ) : (localMaskRoot m)^2=(maskValue m : LocalField) := by
  rw [localMaskRoot,← map_pow,← map_pow,maskRoot_sq,map_ratCast,map_ratCast]

theorem localMaskRoot_ne_zero (m : ℕ) : localMaskRoot m≠0 := by
  apply (map_ne_zero retainedEmbedding).mpr
  apply (map_ne_zero (algebraMap GenusField RetainedField)).mpr
  unfold maskRoot
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split
  · exact roots_ne_zero i
  · exact one_ne_zero

theorem localMaskRoot_action (σ : Gal(LocalField/ℚ_[2])) (m : ℕ) :
    σ (localMaskRoot m)=binarySign (maskCharacter m (model σ).base)*localMaskRoot m := by
  calc
    σ (localMaskRoot m)=retainedEmbedding ((restriction σ)
        (algebraMap GenusField RetainedField (maskRoot m))) :=
      (RationalGaloisBaseChange.restriction_commutes RetainedField ℚ_[2] σ
        (algebraMap GenusField RetainedField (maskRoot m))).symm
    _ = _ := by
      rw [restrict_genusVector,signAutomorphism_maskRoot,map_mul,map_mul]
      simp only [binarySign,map_intCast,← model_base]
      rfl

/-- Every actual Q₂ squareclass relation holds for the actual local Galois signs. -/
theorem character_eq_zero_of_isSquare (σ : Gal(LocalField/ℚ_[2])) (m : ℕ)
    (hm : IsSquare (maskValue m : ℚ_[2])) : maskCharacter m (model σ).base=0 := by
  obtain ⟨a,ha⟩ := hm.exists_sq
  have hs : (localMaskRoot m)^2=(algebraMap ℚ_[2] LocalField a)^2 := by
    rw [localMaskRoot_sq,← map_pow,← ha,map_ratCast]
  have hfixed : σ (localMaskRoot m)=localMaskRoot m := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · rw [h,σ.commutes]
    · rw [h,map_neg,σ.commutes]
  apply binarySign_injective (E := LocalField)
  rw [binarySign_zero]
  apply mul_right_cancel₀ (localMaskRoot_ne_zero m)
  rw [one_mul,← localMaskRoot_action,hfixed]

/-- The actual local genus-coordinate inclusion F₂³ → F₂⁷. -/
def localBase (v : Fin 3 → ZMod 2) : Fin 7 → ZMod 2 :=
  ![v 0,v 1,v 0+v 2,v 2,v 0,v 0+v 2,v 2]

theorem localBase_certificate : ∀ v : Fin 7 → ZMod 2,
    maskCharacter 13 v=0 → maskCharacter 17 v=0 →
    maskCharacter 41 v=0 → maskCharacter 72 v=0 →
    v=localBase (fun i => v (independentIndex i)) := by decide +kernel

theorem model_base_shape (σ : Gal(LocalField/ℚ_[2])) :
    (model σ).base=localBase (signMap σ).toAdd := by
  have hvals : maskValue 13= -15 ∧ maskValue 17= -7 ∧
      maskValue 41= -55 ∧ maskValue 72=65 := by decide +kernel
  have hs := PadicTwo.genus_relations
  apply localBase_certificate
  · apply character_eq_zero_of_isSquare
    simpa only [hvals.1,Rat.cast_neg,Rat.cast_ofNat] using hs.1
  · apply character_eq_zero_of_isSquare
    simpa only [hvals.2.1,Rat.cast_neg,Rat.cast_ofNat] using hs.2.1
  · apply character_eq_zero_of_isSquare
    simpa only [hvals.2.2.1,Rat.cast_neg,Rat.cast_ofNat] using hs.2.2.1
  · apply character_eq_zero_of_isSquare
    simpa only [hvals.2.2.2,Rat.cast_ofNat] using hs.2.2.2

/-- The specified genus coordinates for the three generators of the local model. -/
def localSign : Fin 3 → Multiplicative (Fin 3 → ZMod 2) :=
  ![Multiplicative.ofAdd ![0,1,0],Multiplicative.ofAdd ![1,0,0],
    Multiplicative.ofAdd ![1,0,1]]

def generator (i : Fin 3) : Gal(LocalField/ℚ_[2]) :=
  Function.surjInv signMap_surjective (localSign i)

theorem generator_sign (i : Fin 3) : signMap (generator i)=localSign i :=
  Function.surjInv_eq signMap_surjective (localSign i)

theorem generator_base (i : Fin 3) :
    (model (generator i)).base=RetainedQuadratic.binaryVector 7 (![2,53,89] i) := by
  rw [model_base_shape,generator_sign]
  have h : ∀ i : Fin 3,localBase (localSign i).toAdd=RetainedQuadratic.binaryVector 7 (![2,53,89] i) := by
    decide +kernel
  exact h i

end UnitDistance.ArithmeticDyadic
