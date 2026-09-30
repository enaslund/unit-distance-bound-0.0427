module

public import UnitDistance.GeneratedQuadraticTower
public import UnitDistance.QuadraticRootFamily
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! A generated actual multiquadratic field of the full degree admits all
independent sign automorphisms. The proof uses actual root actions, generation,
and cardinality, without expanding iterated quadratic field instances. -/
noncomputable section
namespace UnitDistance.Multiquadratic
variable {E : Type*} [Field E] [CharZero E] [Algebra ℚ E]
  (r : Fin 7 → ℚ) (x : Fin 7 → E)
  (hx : ∀ i, (x i)^2=(r i : E))
  (hn : ∀ i, x i≠0)
  (hg : Algebra.adjoin ℚ (radicalSet (L := E) r Finset.univ)=⊤)

/-- The actual root action determines its binary sign. -/
def actualRootCharacter (σ : Gal(E/ℚ)) (i : Fin 7) : ZMod 2 :=
  by classical exact if σ (x i)=x i then 0 else 1

include hx in
theorem actualRootCharacter_action (σ : Gal(E/ℚ)) (i : Fin 7) :
    σ (x i)=binarySign (actualRootCharacter x σ i)*x i := by
  classical
  have hs : (σ (x i))^2=(x i)^2 := by rw [← map_pow,hx i,map_ratCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · simp [actualRootCharacter,h,binarySign,binarySignInteger]
  · by_cases he : σ (x i)=x i
    · simp [actualRootCharacter,he,binarySign,binarySignInteger]
    · simp [actualRootCharacter,he,binarySign,binarySignInteger,h]

include hx hg in
theorem generated_roots_aut_ext {σ τ : Gal(E/ℚ)}
    (h : ∀ i, σ (x i)=τ (x i)) : σ=τ := by
  let S : Subalgebra ℚ E := {
    carrier := {z | σ z=τ z}
    zero_mem' := by simp
    one_mem' := by simp
    add_mem' := by
      intro a b ha hb
      change σ a=τ a at ha
      change σ b=τ b at hb
      change σ (a+b)=τ (a+b)
      simp only [map_add,ha,hb]
    mul_mem' := by
      intro a b ha hb
      change σ a=τ a at ha
      change σ b=τ b at hb
      change σ (a*b)=τ (a*b)
      simp only [map_mul,ha,hb]
    algebraMap_mem' := by
      intro q
      change σ (algebraMap ℚ E q)=τ (algebraMap ℚ E q)
      rw [σ.commutes,τ.commutes] }
  have hle : Algebra.adjoin ℚ (radicalSet (L := E) r Finset.univ)≤S := by
    apply Algebra.adjoin_le_iff.mpr
    rintro z ⟨i,hi,hz⟩
    have hs : z^2=(x i)^2 := hz.trans (by simpa using (hx i).symm)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
    · change σ z=τ z
      simpa only [he] using h i
    · change σ z=τ z
      simpa only [he,map_neg] using congrArg Neg.neg (h i)
  rw [hg] at hle
  ext z
  exact hle (show z∈(⊤:Subalgebra ℚ E) from trivial)

include hx hg in
theorem actualRootCharacter_injective : Function.Injective (actualRootCharacter x) := by
  intro σ τ h
  apply generated_roots_aut_ext r x hx hg
  intro i
  rw [actualRootCharacter_action r x hx,actualRootCharacter_action r x hx,h]

include hx hg in
theorem actualRootCharacter_bijective (hc : Nat.card (Gal(E/ℚ))=128) :
    Function.Bijective (actualRootCharacter x) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨actualRootCharacter_injective r x hx hg,?_⟩
  rw [hc]
  simp [Nat.card_eq_fintype_card,Fintype.card_fun,ZMod.card]

/-- Actual sign maps recovered from the bijective action on actual roots. -/
def generatedRootEquiv (hc : Nat.card (Gal(E/ℚ))=128) :
    Gal(E/ℚ) ≃ (Fin 7 → ZMod 2) :=
  Equiv.ofBijective (actualRootCharacter x) (actualRootCharacter_bijective r x hx hg hc)

/-- An actual full root/sign family obtained from generation and degree. -/
def generatedRootFamily (hc : Nat.card (Gal(E/ℚ))=128) : RootFamily r 7 E where
  roots := x
  automorphism := (generatedRootEquiv r x hx hg hc).symm
  square i hi := hx i
  action v i hi := by
    have h := actualRootCharacter_action r x hx ((generatedRootEquiv r x hx hg hc).symm v) i
    have he : actualRootCharacter x ((generatedRootEquiv r x hx hg hc).symm v)=v :=
      (generatedRootEquiv r x hx hg hc).apply_symm_apply v
    simpa only [he] using h
  involutive v := by
    have hh : ∀ i, ((generatedRootEquiv r x hx hg hc).symm v)
        (((generatedRootEquiv r x hx hg hc).symm v) (x i))=x i := by
      intro i
      have h : actualRootCharacter x ((generatedRootEquiv r x hx hg hc).symm v)=v :=
        (generatedRootEquiv r x hx hg hc).apply_symm_apply v
      rw [actualRootCharacter_action r x hx,map_mul,rational_map_binarySign,
        actualRootCharacter_action r x hx,h]
      rw [← mul_assoc,← pow_two,binarySign_sq,one_mul]
    have he : (generatedRootEquiv r x hx hg hc).symm v *
        (generatedRootEquiv r x hx hg hc).symm v = 1 := by
      apply generated_roots_aut_ext r x hx hg
      simpa only [AlgEquiv.mul_apply,AlgEquiv.one_apply] using hh
    intro z
    simpa only [AlgEquiv.mul_apply,AlgEquiv.one_apply] using AlgEquiv.congr_fun he z

end UnitDistance.Multiquadratic
