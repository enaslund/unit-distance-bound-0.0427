module

public import UnitDistance.PadicTwoNormCatalog
public import UnitDistance.GeneratedQuadraticExponent

@[expose] public section
set_option backward.privateInPublic true


/-! An actual Q₂ Galois field of degree256, constructed from three independent
squareclasses and five independently detected norm extensions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.PadicTwoQuadratic
open Multiquadratic PadicTwoGenus PadicTwoNormCatalog
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev E := PadicTwoGenus.GenusField

def selected (w : Fin 5 → ZMod 2) : E := ∏ i,if w i=0 then 1 else alpha i
def selectedMultiplier (w : Fin 5 → ZMod 2) (v : Fin 3 → ZMod 2) : E :=
  ∏ i,if w i=0 then 1 else multiplier i v

theorem selected_ne_zero (w : Fin 5 → ZMod 2) : selected w≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split
  · exact one_ne_zero
  · exact alpha_ne_zero i

theorem selected_twist (w : Fin 5 → ZMod 2) (v : Fin 3 → ZMod 2) :
    selected w*(selectedMultiplier w v)^2=signAutomorphism v (selected w) := by
  unfold selected selectedMultiplier
  rw [map_prod,← Finset.prod_pow,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split
  · simp
  · exact multiplier_twist i v

theorem selected_norm (w : Fin 5 → ZMod 2) (v : Fin 3 → ZMod 2) :
    selectedMultiplier w v*signAutomorphism v (selectedMultiplier w v)=
      binarySign (∑ i,form i v*w i) := by
  unfold selectedMultiplier
  rw [map_prod,← Finset.prod_mul_distrib,binarySign_sum]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hw : w i=0
  · simp [hw]
  · have ho : w i=1 := ((by decide : ∀ t : ZMod 2,t=0 ∨ t=1) (w i)).resolve_left hw
    simpa [ho] using multiplier_norm i v

theorem selected_nonsquare (w : Fin 5 → ZMod 2) (hw : w≠0) :
    KummerInvariant.Nonsquare (selected w) := by
  have hv : ∃ v : Fin 3 → ZMod 2,∑ i,form i v*w i≠0 := by
    by_contra h
    push_neg at h
    exact hw (forms_detect w h)
  obtain ⟨v,hv⟩ := hv
  apply KummerInvariant.nonsquare_of_twisted_norm (signAutomorphism v)
    (signAutomorphism_involutive v) (selected w) (selectedMultiplier w v)
    (selected_ne_zero w) (selected_twist w v)
  rw [selected_norm]
  intro h
  apply hv
  apply binarySign_injective (E:=E)
  simpa using h

theorem products_nonsquare (s : Finset (Fin 5)) (hs : s.Nonempty) :
    ¬IsSquare (∏ i∈s,alpha i) := by
  let w : Fin 5 → ZMod 2 := fun i => if i∈s then 1 else 0
  have hw : w≠0 := by
    obtain ⟨i,hi⟩ := hs
    intro h
    have hh := congrFun h i
    simp [w,hi] at hh
  have he : selected w=∏ i∈s,alpha i := by
    classical
    simp [selected,w]
  intro h
  obtain ⟨r,hr⟩ := h
  apply selected_nonsquare w hw r
  simpa [he,pow_two] using hr.symm

theorem alpha_invariant (i : Fin 5) (σ : Gal(E/ℚ_[2])) :
    ∃ u : E,alpha i*u^2=σ (alpha i) := by
  let v := (signEquiv σ).toAdd
  have hσ : signAutomorphism v=σ := signEquiv.symm_apply_apply σ
  refine ⟨multiplier i v,?_⟩
  rw [← hσ]
  exact multiplier_twist i v

def quadraticTower : GeneratedGaloisTower ℚ_[2] alpha Finset.univ :=
  Classical.choice (exists_generatedGaloisTower ℚ_[2] alpha alpha_ne_zero
    products_nonsquare alpha_invariant Finset.univ)

abbrev QuadraticField := quadraticTower.Carrier
instance : Field QuadraticField := quadraticTower.field
instance : CharZero QuadraticField := quadraticTower.charZero
instance : Algebra E QuadraticField := quadraticTower.algebra
instance : Algebra ℚ_[2] QuadraticField := quadraticTower.baseAlgebra
instance : IsScalarTower ℚ_[2] E QuadraticField := quadraticTower.scalarTower
instance : Module.Finite E QuadraticField := quadraticTower.finite
instance : Module.Finite ℚ_[2] QuadraticField := Module.Finite.trans E QuadraticField
instance : IsGalois ℚ_[2] QuadraticField := quadraticTower.baseGalois

theorem relative_degree : Module.finrank E QuadraticField=32 := by simpa using quadraticTower.degree

theorem degree : Module.finrank ℚ_[2] QuadraticField=256 := by
  rw [← Module.finrank_mul_finrank ℚ_[2] E QuadraticField,PadicTwoGenus.degree,relative_degree]

theorem galoisGroup_card : Nat.card Gal(QuadraticField/ℚ_[2])=256 := by
  rw [IsGalois.card_aut_eq_finrank,degree]

theorem isPGroup : IsPGroup 2 Gal(QuadraticField/ℚ_[2]) := IsPGroup.of_card (n:=8) galoisGroup_card

end UnitDistance.PadicTwoQuadratic
