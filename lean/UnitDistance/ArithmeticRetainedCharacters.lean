module

public import UnitDistance.ArithmeticRetainedQuadraticAction

@[expose] public section
set_option backward.privateInPublic true


/-! The actual relative Galois group of the retained field, with all twelve
independent signs recovered from its action on actual defining radicals. -/
noncomputable section
namespace UnitDistance.ArithmeticRetained
open ArithmeticChosenGenus Multiquadratic

def retainedRoot (j : Fin 12) : RetainedField :=
  (retainedField_contains_radical j).choose

theorem retainedRoot_sq (j : Fin 12) :
    (retainedRoot j)^2=algebraMap GenusField RetainedField (retainedRadicand j) :=
  (retainedField_contains_radical j).choose_spec

theorem retainedRoot_ne_zero (j : Fin 12) : retainedRoot j≠0 := by
  intro h
  have hh := retainedRoot_sq j
  rw [h,zero_pow (by decide : 2≠0)] at hh
  exact retainedRadicand_ne_zero j ((algebraMap GenusField RetainedField).injective
    (hh.symm.trans (map_zero _).symm))

/-- Forgetting relative scalars gives the actual absolute automorphism. -/
def absoluteOfRelative : Gal(RetainedField/GenusField) →* Gal(RetainedField/ℚ) where
  toFun σ := σ.restrictScalars ℚ
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem absoluteOfRelative_apply (σ : Gal(RetainedField/GenusField)) (x : RetainedField) :
    absoluteOfRelative σ x=σ x := rfl

/-- Actual sign of a relative automorphism on one retained radical. -/
def relativeCharacter (σ : Gal(RetainedField/GenusField)) (j : Fin 12) : ZMod 2 :=
  by classical exact if σ (retainedRoot j)=retainedRoot j then 0 else 1

theorem relativeCharacter_action (σ : Gal(RetainedField/GenusField)) (j : Fin 12) :
    σ (retainedRoot j)=binarySign (relativeCharacter σ j)*retainedRoot j := by
  classical
  have hs : (σ (retainedRoot j))^2=(retainedRoot j)^2 := by
    rw [← map_pow,retainedRoot_sq,σ.commutes]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · simp [relativeCharacter,h,binarySign,binarySignInteger]
  · by_cases he : σ (retainedRoot j)=retainedRoot j
    · simp [relativeCharacter,he,binarySign,binarySignInteger]
    · simp [relativeCharacter,he,binarySign,binarySignInteger,h]

theorem relative_aut_ext {σ τ : Gal(RetainedField/GenusField)}
    (h : ∀ j, σ (retainedRoot j)=τ (retainedRoot j)) : σ=τ := by
  have he : absoluteOfRelative σ=absoluteOfRelative τ := by
    apply retained_aut_ext
    · intro a
      change σ (algebraMap GenusField RetainedField a)=τ (algebraMap GenusField RetainedField a)
      rw [σ.commutes,τ.commutes]
    · rintro x ⟨j,hj,hx⟩
      have hs : x^2=(retainedRoot j)^2 := hx.trans (retainedRoot_sq j).symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
      · simpa only [hs,absoluteOfRelative_apply] using h j
      · simpa only [hs,absoluteOfRelative_apply,map_neg] using congrArg Neg.neg (h j)
  ext x
  exact AlgEquiv.congr_fun he x

theorem relativeCharacter_injective : Function.Injective relativeCharacter := by
  intro σ τ h
  apply relative_aut_ext
  intro j
  rw [relativeCharacter_action,relativeCharacter_action,h]

/-- The actual relative sign map is a group homomorphism. -/
def relativeSignHom : Gal(RetainedField/GenusField) →* Multiplicative (Fin 12 → ZMod 2) where
  toFun σ := Multiplicative.ofAdd (relativeCharacter σ)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext j
    simp [relativeCharacter]
  map_mul' σ τ := by
    apply Multiplicative.toAdd.injective
    funext j
    apply binarySign_injective (E := RetainedField)
    apply mul_right_cancel₀ (retainedRoot_ne_zero j)
    change binarySign (relativeCharacter (σ*τ) j)*retainedRoot j =
      binarySign (relativeCharacter σ j+relativeCharacter τ j)*retainedRoot j
    rw [← relativeCharacter_action,AlgEquiv.mul_apply,relativeCharacter_action τ j,
      map_mul,show σ (binarySign (relativeCharacter τ j))=binarySign (relativeCharacter τ j) from by
        simp [binarySign],relativeCharacter_action σ j,binarySign_add]
    ring

theorem relativeSignHom_bijective : Function.Bijective relativeSignHom := by
  letI : IsGalois GenusField RetainedField := fullRetainedTower.galois
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨fun _ _ h => relativeCharacter_injective (congrArg Multiplicative.toAdd h),?_⟩
  rw [IsGalois.card_aut_eq_finrank,retainedField_relative_degree]
  simp [Nat.card_eq_fintype_card,Fintype.card_multiplicative,Fintype.card_fun,ZMod.card]

/-- All actual relative signs, as an equivalence of actual groups. -/
def relativeGaloisEquiv : Gal(RetainedField/GenusField) ≃* Multiplicative (Fin 12 → ZMod 2) :=
  MulEquiv.ofBijective relativeSignHom relativeSignHom_bijective

/-- The actual central automorphism with the prescribed twelve root signs. -/
def centralSignHom : Multiplicative (Fin 12 → ZMod 2) →* Gal(RetainedField/ℚ) :=
  absoluteOfRelative.comp relativeGaloisEquiv.symm.toMonoidHom

theorem centralSignHom_action (v : Multiplicative (Fin 12 → ZMod 2)) (j : Fin 12) :
    centralSignHom v (retainedRoot j)=binarySign (v.toAdd j)*retainedRoot j := by
  have he := congrArg Multiplicative.toAdd (relativeGaloisEquiv.apply_symm_apply v)
  change relativeCharacter (relativeGaloisEquiv.symm v)=v.toAdd at he
  change relativeGaloisEquiv.symm v (retainedRoot j)=_
  rw [relativeCharacter_action,he]

theorem centralSignHom_fixes_genus (v : Multiplicative (Fin 12 → ZMod 2)) (a : GenusField) :
    centralSignHom v (algebraMap GenusField RetainedField a)=algebraMap GenusField RetainedField a :=
  (relativeGaloisEquiv.symm v).commutes a

theorem centralSignHom_central (v : Multiplicative (Fin 12 → ZMod 2)) (σ : Gal(RetainedField/ℚ)) :
    Commute (centralSignHom v) σ :=
  retained_relative_aut_central _ σ (centralSignHom_fixes_genus v)

theorem centralSignHom_injective : Function.Injective centralSignHom := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext j
  apply binarySign_injective (E := RetainedField)
  apply mul_right_cancel₀ (retainedRoot_ne_zero j)
  rw [← centralSignHom_action,← centralSignHom_action,h]

end UnitDistance.ArithmeticRetained
