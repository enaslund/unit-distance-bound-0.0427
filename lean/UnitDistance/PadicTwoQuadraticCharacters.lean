module

public import UnitDistance.PadicTwoQuadraticAction

@[expose] public section
set_option backward.privateInPublic true


/-! The actual relative Galois group of the local quadratic field, with all five
independent signs recovered from its action on actual defining radicals. -/
noncomputable section
namespace UnitDistance.PadicTwoQuadratic
open Multiquadratic PadicTwoGenus PadicTwoNormCatalog
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
instance : IsGalois E QuadraticField := quadraticTower.galois

def quadraticRoot (j : Fin 5) : QuadraticField :=
  (quadraticTower.isSquare_radical j (Finset.mem_univ j) (alpha_ne_zero j)).choose

theorem quadraticRoot_sq (j : Fin 5) :
    (quadraticRoot j)^2=algebraMap E QuadraticField (alpha j) := by
  simpa [quadraticRoot,pow_two] using
    (quadraticTower.isSquare_radical j (Finset.mem_univ j) (alpha_ne_zero j)).choose_spec.symm

theorem quadraticRoot_ne_zero (j : Fin 5) : quadraticRoot j≠0 := by
  intro h
  have hh := quadraticRoot_sq j
  rw [h,zero_pow (by decide : 2≠0)] at hh
  exact alpha_ne_zero j ((algebraMap E QuadraticField).injective
    (hh.symm.trans (map_zero _).symm))

/-- Forgetting relative scalars gives the actual absolute automorphism. -/
def absoluteOfRelative : Gal(QuadraticField/E) →* Gal(QuadraticField/ℚ_[2]) where
  toFun σ := σ.restrictScalars ℚ_[2]
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem absoluteOfRelative_apply (σ : Gal(QuadraticField/E)) (x : QuadraticField) :
    absoluteOfRelative σ x=σ x := rfl

/-- Actual sign of a relative automorphism on one local quadratic radical. -/
def relativeCharacter (σ : Gal(QuadraticField/E)) (j : Fin 5) : ZMod 2 :=
  by classical exact if σ (quadraticRoot j)=quadraticRoot j then 0 else 1

theorem relativeCharacter_action (σ : Gal(QuadraticField/E)) (j : Fin 5) :
    σ (quadraticRoot j)=binarySign (relativeCharacter σ j)*quadraticRoot j := by
  classical
  have hs : (σ (quadraticRoot j))^2=(quadraticRoot j)^2 := by
    rw [← map_pow,quadraticRoot_sq,σ.commutes]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · simp [relativeCharacter,h,binarySign,binarySignInteger]
  · by_cases he : σ (quadraticRoot j)=quadraticRoot j
    · simp [relativeCharacter,he,binarySign,binarySignInteger]
    · simp [relativeCharacter,he,binarySign,binarySignInteger,h]

theorem relative_aut_ext {σ τ : Gal(QuadraticField/E)}
    (h : ∀ j, σ (quadraticRoot j)=τ (quadraticRoot j)) : σ=τ := by
  have he : absoluteOfRelative σ=absoluteOfRelative τ := by
    apply quadraticTower.aut_ext
    · intro a
      change σ (algebraMap E QuadraticField a)=τ (algebraMap E QuadraticField a)
      rw [σ.commutes,τ.commutes]
    · rintro x ⟨j,hj,hx⟩
      have hs : x^2=(quadraticRoot j)^2 := hx.trans (quadraticRoot_sq j).symm
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
def relativeSignHom : Gal(QuadraticField/E) →* Multiplicative (Fin 5 → ZMod 2) where
  toFun σ := Multiplicative.ofAdd (relativeCharacter σ)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext j
    simp [relativeCharacter]
  map_mul' σ τ := by
    apply Multiplicative.toAdd.injective
    funext j
    apply binarySign_injective (E := QuadraticField)
    apply mul_right_cancel₀ (quadraticRoot_ne_zero j)
    change binarySign (relativeCharacter (σ*τ) j)*quadraticRoot j =
      binarySign (relativeCharacter σ j+relativeCharacter τ j)*quadraticRoot j
    rw [← relativeCharacter_action,AlgEquiv.mul_apply,relativeCharacter_action τ j,
      map_mul,show σ (binarySign (relativeCharacter τ j))=binarySign (relativeCharacter τ j) from by
        simp [binarySign],relativeCharacter_action σ j,binarySign_add]
    ring

theorem relativeSignHom_bijective : Function.Bijective relativeSignHom := by
  letI : IsGalois E QuadraticField := quadraticTower.galois
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨fun _ _ h => relativeCharacter_injective (congrArg Multiplicative.toAdd h),?_⟩
  rw [IsGalois.card_aut_eq_finrank,relative_degree]
  simp [Nat.card_eq_fintype_card,Fintype.card_multiplicative,Fintype.card_fun,ZMod.card]

/-- All actual relative signs, as an equivalence of actual groups. -/
def relativeGaloisEquiv : Gal(QuadraticField/E) ≃* Multiplicative (Fin 5 → ZMod 2) :=
  MulEquiv.ofBijective relativeSignHom relativeSignHom_bijective

/-- The actual central automorphism with the prescribed five root signs. -/
def centralSignHom : Multiplicative (Fin 5 → ZMod 2) →* Gal(QuadraticField/ℚ_[2]) :=
  absoluteOfRelative.comp relativeGaloisEquiv.symm.toMonoidHom

theorem centralSignHom_action (v : Multiplicative (Fin 5 → ZMod 2)) (j : Fin 5) :
    centralSignHom v (quadraticRoot j)=binarySign (v.toAdd j)*quadraticRoot j := by
  have he := congrArg Multiplicative.toAdd (relativeGaloisEquiv.apply_symm_apply v)
  change relativeCharacter (relativeGaloisEquiv.symm v)=v.toAdd at he
  change relativeGaloisEquiv.symm v (quadraticRoot j)=_
  rw [relativeCharacter_action,he]

theorem centralSignHom_fixes_genus (v : Multiplicative (Fin 5 → ZMod 2)) (a : E) :
    centralSignHom v (algebraMap E QuadraticField a)=algebraMap E QuadraticField a :=
  (relativeGaloisEquiv.symm v).commutes a

theorem centralSignHom_central (v : Multiplicative (Fin 5 → ZMod 2)) (σ : Gal(QuadraticField/ℚ_[2])) :
    Commute (centralSignHom v) σ :=
  quadraticTower.aut_commute (fun i _ => alpha_invariant i) _ σ (centralSignHom_fixes_genus v)

theorem centralSignHom_injective : Function.Injective centralSignHom := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext j
  apply binarySign_injective (E := QuadraticField)
  apply mul_right_cancel₀ (quadraticRoot_ne_zero j)
  rw [← centralSignHom_action,← centralSignHom_action,h]

end UnitDistance.PadicTwoQuadratic
