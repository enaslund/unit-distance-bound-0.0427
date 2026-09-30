module

public import UnitDistance.GeneratedQuadraticTower
public import UnitDistance.QuadraticRootCharacterSurjectivity

@[expose] public section
set_option backward.privateInPublic true


/-! Actual independent sign automorphisms over an arbitrary characteristic-zero
base field, obtained from genuine squareclass independence. -/
noncomputable section
namespace UnitDistance.Multiquadratic
variable {K E ι : Type*} [Field K] [CharZero K] [Field E] [CharZero E] [Algebra K E]
  [Fintype ι] [DecidableEq ι] [FiniteDimensional K E] [IsGalois K E]
  (d : ι → K) (r : ι → E)
  (hr : ∀ i,(r i)^2=algebraMap K E (d i)) (hn : ∀ i,r i≠0)

def rootCharacter (σ : Gal(E/K)) (i : ι) : ZMod 2 :=
  by classical exact if σ (r i)=r i then 0 else 1

include hr in
theorem rootCharacter_action (σ : Gal(E/K)) (i : ι) :
    σ (r i)=binarySign (rootCharacter r σ i)*r i := by
  classical
  have hs : (σ (r i))^2=(r i)^2 := by rw [← map_pow,hr,σ.commutes]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · simp [rootCharacter,h,binarySign,binarySignInteger]
  · by_cases he : σ (r i)=r i
    · simp [rootCharacter,he,binarySign,binarySignInteger]
    · simp [rootCharacter,he,binarySign,binarySignInteger,h]

def rootSignHom : Gal(E/K) →* Multiplicative (ι → ZMod 2) where
  toFun σ := Multiplicative.ofAdd (rootCharacter r σ)
  map_one' := by
    classical
    apply Multiplicative.toAdd.injective
    funext i
    simp [rootCharacter]
  map_mul' σ τ := by
    apply Multiplicative.toAdd.injective
    funext i
    apply binarySign_injective (E:=E)
    apply mul_right_cancel₀ (hn i)
    change binarySign (rootCharacter r (σ*τ) i)*r i=
      binarySign (rootCharacter r σ i+rootCharacter r τ i)*r i
    rw [← rootCharacter_action d r hr]
    change σ (τ (r i))=binarySign (rootCharacter r σ i+rootCharacter r τ i)*r i
    rw [rootCharacter_action d r hr τ,map_mul,binarySign,map_intCast,
      ← binarySign,rootCharacter_action d r hr σ,binarySign_add]
    ring

include hr hn in
theorem rootSignHom_surjective
    (hind : ∀ w : ι → ZMod 2,IsSquare (∏ i,d i^(w i).val) → w=0) :
    Function.Surjective (rootSignHom d r hr hn) := by
  apply signHom_surjective_of_products r d hr
  · exact rootCharacter_action d r hr
  · exact hind

include hr in
theorem generated_aut_ext
    (hgen : Algebra.adjoin K (radicalSet (L:=E) d Finset.univ)=⊤)
    {σ τ : Gal(E/K)} (h : ∀ i,σ (r i)=τ (r i)) : σ=τ := by
  have he : σ.toAlgHom=τ.toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    rintro z ⟨i,hi,hz⟩
    change σ z=τ z
    have hs : z^2=(r i)^2 := hz.trans (hr i).symm
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
    · simpa only [he] using h i
    · simpa only [he,map_neg] using congrArg Neg.neg (h i)
  exact AlgEquiv.ext (fun z => congrArg (fun f : E →ₐ[K] E => f z) he)

include hr in
theorem rootSignHom_injective
    (hgen : Algebra.adjoin K (radicalSet (L:=E) d Finset.univ)=⊤) :
    Function.Injective (rootSignHom d r hr hn) := by
  intro σ τ h
  apply generated_aut_ext d r hr hgen
  intro i
  rw [rootCharacter_action d r hr,rootCharacter_action d r hr]
  have he := congrArg (fun v : Multiplicative (ι → ZMod 2) => v.toAdd i) h
  exact congrArg (fun v : ZMod 2 => binarySign v*r i) he

end UnitDistance.Multiquadratic
