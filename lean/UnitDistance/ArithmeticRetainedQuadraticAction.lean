module

public import UnitDistance.ArithmeticRetainedGalois
public import UnitDistance.QuadraticLiftSquare

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual retained-field quadratic signs

Every automorphism of the actual retained field has its actual genus sign
vector. Its square acts on each retained radical by the independently
computed catalog quadratic form, regardless of which lift was chosen.
-/
noncomputable section
namespace UnitDistance.ArithmeticRetained
open ArithmeticChosenGenus ArithmeticCatalog Multiquadratic

/-- The actual genus coordinates of an actual retained-field automorphism. -/
def genusVector (σ : Gal(RetainedField/ℚ)) : Fin 7 → ZMod 2 :=
  (genusGaloisEquiv.symm (σ.restrictNormal GenusField)).toAdd

theorem signAutomorphism_genusVector (σ : Gal(RetainedField/ℚ)) :
    signAutomorphism (genusVector σ)=σ.restrictNormal GenusField := by
  exact genusGaloisEquiv.apply_symm_apply _

/-- The actual restriction, expressed on every actual element of the genus field. -/
theorem restrict_genusVector (σ : Gal(RetainedField/ℚ)) (a : GenusField) :
    σ (algebraMap GenusField RetainedField a)=
      algebraMap GenusField RetainedField (signAutomorphism (genusVector σ) a) := by
  rw [signAutomorphism_genusVector]
  exact (AlgEquiv.restrictNormal_commutes σ GenusField a).symm

/-- The actual squared lift has exactly the catalog quadratic sign. -/
theorem square_action_on_radical (σ : Gal(RetainedField/ℚ)) (j : Fin 12)
    (x : RetainedField) (hx : x^2=algebraMap GenusField RetainedField (retainedRadicand j)) :
    (σ^2) x = binarySign
      (CatalogSquareclassData.wordForm (CatalogSquareclassData.retainedWords j) (genusVector σ))*x := by
  exact square_on_root_of_twisted_norm
    (signAutomorphism (genusVector σ)).toRingEquiv σ.toRingEquiv
    (restrict_genusVector σ) hx
    (wordMultiplier_twist (CatalogSquareclassData.retainedWords j) (genusVector σ)) _
    (wordMultiplier_twisted_norm (CatalogSquareclassData.retainedWords j) (genusVector σ))

/-- Actual genus coordinates are additive under composition. -/
theorem genusVector_mul (σ τ : Gal(RetainedField/ℚ)) :
    genusVector (σ*τ)=genusVector σ+genusVector τ := by
  change (genusGaloisEquiv.symm ((AlgEquiv.restrictNormalHom GenusField) (σ*τ))).toAdd = _
  rw [map_mul,map_mul]
  rfl

/-- Actual automorphisms are determined by the genus field and all defining radicals. -/
theorem retained_aut_ext : ∀ (σ τ : Gal(RetainedField/ℚ)),
    (∀ a : GenusField, σ (algebraMap GenusField RetainedField a)=
      τ (algebraMap GenusField RetainedField a)) →
    (∀ x ∈ radicalSet (L := RetainedField) retainedRadicand Finset.univ, σ x=τ x) → σ=τ := by
  rw [← retainedTower_baseAlgebra_eq]
  exact fullRetainedTower.aut_ext

/-- Every actual automorphism square fixes the actual genus field. -/
theorem retained_aut_square_fixes_genus : ∀ (σ : Gal(RetainedField/ℚ)) (x : GenusField),
    (σ^2) (algebraMap GenusField RetainedField x)=algebraMap GenusField RetainedField x := by
  rw [← retainedTower_baseAlgebra_eq]
  exact fullRetainedTower.aut_square_fixes_base every_automorphism_involutive

/-- Vanishing of the actual twelve forms forces an actual lift to be an involution. -/
theorem square_eq_one_of_forms_zero (σ : Gal(RetainedField/ℚ))
    (h : ∀ j : Fin 12,
      CatalogSquareclassData.wordForm (CatalogSquareclassData.retainedWords j) (genusVector σ)=0) :
    σ^2=1 := by
  apply retained_aut_ext
  · intro x
    exact retained_aut_square_fixes_genus σ x
  · rintro x ⟨j,hj,hx⟩
    change (σ^2) x=x
    rw [square_action_on_radical σ j x hx,h,binarySign_zero,one_mul]

/-- A group identity expressing the actual commutator through three actual squares. -/
theorem commutator_eq_three_squares (σ τ : Gal(RetainedField/ℚ)) :
    σ⁻¹*τ⁻¹*σ*τ=σ^2*τ^2*(σ*τ)^2 := by
  have hcube (g : Gal(RetainedField/ℚ)) : g^3=g⁻¹ := by
    apply mul_right_cancel (b := g)
    rw [inv_mul_cancel]
    simpa only [← pow_succ] using retained_aut_pow_four g
  symm
  calc
    σ^2*τ^2*(σ*τ)^2=σ^2*(τ^2*σ)*τ*σ*τ := by simp only [pow_two,mul_assoc]
    _ = σ^2*(σ*τ^2)*τ*σ*τ := by rw [(retained_aut_square_central τ σ).eq]
    _ = σ^3*τ^3*σ*τ := by group
    _ = _ := by rw [hcube σ,hcube τ]

/-- The actual commutator has the polarized catalog sign on every radical. -/
theorem commutator_action_on_radical (σ τ : Gal(RetainedField/ℚ)) (j : Fin 12)
    (x : RetainedField) (hx : x^2=algebraMap GenusField RetainedField (retainedRadicand j)) :
    (σ⁻¹*τ⁻¹*σ*τ) x = binarySign
      (CatalogSquareclassData.wordForm (CatalogSquareclassData.retainedWords j)
        (genusVector σ+genusVector τ) +
       CatalogSquareclassData.wordForm (CatalogSquareclassData.retainedWords j) (genusVector σ) +
       CatalogSquareclassData.wordForm (CatalogSquareclassData.retainedWords j) (genusVector τ))*x := by
  rw [commutator_eq_three_squares]
  simp only [AlgEquiv.mul_apply,square_action_on_radical _ j x hx,
    map_mul,map_binarySign,genusVector_mul,binarySign_add]
  ring

/-- The inverse restriction has the negative genus vector. -/
theorem genusVector_inv (σ : Gal(RetainedField/ℚ)) :
    genusVector σ⁻¹ = -genusVector σ := by
  change (genusGaloisEquiv.symm ((AlgEquiv.restrictNormalHom GenusField) σ⁻¹)).toAdd = _
  rw [map_inv,map_inv]
  rfl

/-- Zero actual genus coordinates mean pointwise fixation of the actual genus field. -/
theorem fixes_genus_of_vector_zero (σ : Gal(RetainedField/ℚ)) (h : genusVector σ=0)
    (a : GenusField) : σ (algebraMap GenusField RetainedField a)=algebraMap GenusField RetainedField a := by
  rw [restrict_genusVector,h]
  have hzero : signAutomorphism (0 : Fin 7 → ZMod 2)=1 := genusSignHom.map_one
  rw [hzero,AlgEquiv.one_apply]

/-- Actual commutators fix the genus field. -/
theorem commutator_genusVector (σ τ : Gal(RetainedField/ℚ)) :
    genusVector (σ⁻¹*τ⁻¹*σ*τ)=0 := by
  simp only [genusVector_mul,genusVector_inv]
  abel

/-- Polar-form vanishing proves commutation of actual field automorphisms. -/
theorem commute_of_polar_zero (σ τ : Gal(RetainedField/ℚ))
    (h : ∀ j : Fin 12,
      CatalogSquareclassData.wordForm (CatalogSquareclassData.retainedWords j)
        (genusVector σ+genusVector τ) +
      CatalogSquareclassData.wordForm (CatalogSquareclassData.retainedWords j) (genusVector σ) +
      CatalogSquareclassData.wordForm (CatalogSquareclassData.retainedWords j) (genusVector τ)=0) :
    Commute σ τ := by
  have he : σ⁻¹*τ⁻¹*σ*τ=1 := by
    apply retained_aut_ext
    · intro a
      exact fixes_genus_of_vector_zero _ (commutator_genusVector σ τ) a
    · rintro x ⟨j,hj,hx⟩
      change (σ⁻¹*τ⁻¹*σ*τ) x=x
      rw [commutator_action_on_radical σ τ j x hx,h,binarySign_zero,one_mul]
  change σ*τ=τ*σ
  calc
    σ*τ=(τ*σ)*(σ⁻¹*τ⁻¹*σ*τ) := by group
    _ = τ*σ := by rw [he,mul_one]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Every retained form has zero diagonal in the seven fixed genus coordinates. -/
theorem retainedForm_basis_zero (i : Fin 7) (j : Fin 12) :
    CatalogSquareclassData.wordForm (CatalogSquareclassData.retainedWords j)
      (Pi.single i 1)=0 := by
  have h : ∀ (i : Fin 7) (j : Fin 12),
      CatalogSquareclassData.wordForm (CatalogSquareclassData.retainedWords j)
        (Pi.single i 1)=0 := by decide +kernel
  exact h i j

/-- Every lift of each of the seven actual genus basis elements is involutive. -/
theorem basis_lift_square (σ : Gal(RetainedField/ℚ)) (i : Fin 7)
    (h : genusVector σ=Pi.single i 1) : σ^2=1 := by
  apply square_eq_one_of_forms_zero
  intro j
  rw [h]
  exact retainedForm_basis_zero i j

end UnitDistance.ArithmeticRetained
