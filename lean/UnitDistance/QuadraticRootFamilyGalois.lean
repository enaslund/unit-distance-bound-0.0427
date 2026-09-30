module

public import UnitDistance.QuadraticRootFamily
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! Actual complete root/sign families determine the full Galois group once
the independently proved degree supplies its cardinality. -/
noncomputable section
namespace UnitDistance.Multiquadratic
variable {r : Fin 7 → ℚ} {E : Type*} [Field E] [CharZero E] [Algebra ℚ E]
namespace RootFamily
variable (A : RootFamily r 7 E) (hr : ∀ i, r i ≠ 0)
include hr

theorem roots_ne_zero (i : Fin 7) : A.roots i ≠ 0 := by
  have h : (r i : E) ≠ 0 := by exact_mod_cast hr i
  intro hz
  have he := A.square i i.isLt
  rw [hz,zero_pow (by decide : 2 ≠ 0)] at he
  exact h he.symm

theorem automorphism_injective : Function.Injective A.automorphism := by
  intro v w h
  funext i
  apply binarySign_injective (E := E)
  apply mul_right_cancel₀ (A.roots_ne_zero hr i)
  rw [← A.action v i i.isLt,← A.action w i i.isLt,h]

theorem automorphism_bijective (hc : Nat.card (Gal(E/ℚ)) = 128) :
    Function.Bijective A.automorphism := by
  letI : Finite (Gal(E/ℚ)) := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨A.automorphism_injective hr,?_⟩
  rw [hc]
  simp [Nat.card_eq_fintype_card,Fintype.card_fun,ZMod.card]

theorem aut_ext (hc : Nat.card (Gal(E/ℚ)) = 128) {σ τ : Gal(E/ℚ)}
    (h : ∀ i, σ (A.roots i)=τ (A.roots i)) : σ=τ := by
  obtain ⟨v,rfl⟩ := (A.automorphism_bijective hr hc).surjective σ
  obtain ⟨w,rfl⟩ := (A.automorphism_bijective hr hc).surjective τ
  congr 1
  funext i
  apply binarySign_injective (E := E)
  apply mul_right_cancel₀ (A.roots_ne_zero hr i)
  simpa only [A.action _ _ (Fin.isLt _)] using h i

def signHom (hc : Nat.card (Gal(E/ℚ)) = 128) :
    Multiplicative (Fin 7 → ZMod 2) →* Gal(E/ℚ) where
  toFun v := A.automorphism v.toAdd
  map_one' := by
    apply A.aut_ext hr hc
    intro i
    simp [A.action _ _ (Fin.isLt _)]
  map_mul' v w := by
    apply A.aut_ext hr hc
    intro i
    change A.automorphism (v.toAdd+w.toAdd) (A.roots i) =
      (A.automorphism v.toAdd*A.automorphism w.toAdd) (A.roots i)
    rw [AlgEquiv.mul_apply,A.action _ _ i.isLt,A.action _ _ i.isLt,map_mul,
      rational_map_binarySign,A.action _ _ i.isLt]
    simp only [Pi.add_apply,binarySign_add]
    ring

def galoisEquiv (hc : Nat.card (Gal(E/ℚ)) = 128) :
    Multiplicative (Fin 7 → ZMod 2) ≃* Gal(E/ℚ) :=
  MulEquiv.ofBijective (A.signHom hr hc)
    ((A.automorphism_bijective hr hc).comp Multiplicative.toAdd.bijective)

include A in
theorem every_automorphism_involutive (hc : Nat.card (Gal(E/ℚ)) = 128)
    (σ : Gal(E/ℚ)) : Function.Involutive σ := by
  obtain ⟨v,rfl⟩ := (A.automorphism_bijective hr hc).surjective σ
  exact A.involutive v

end RootFamily
end UnitDistance.Multiquadratic
