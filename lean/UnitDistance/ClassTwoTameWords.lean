module

public import UnitDistance.GroupAugmentationClassTwo
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Actual odd tame words in any characteristic-two bilinear group.
Their values depend only on the elementary coordinates of their lifts. -/
noncomputable section
namespace UnitDistance.ClassTwo.Tame
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
variable (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)

abbrev Q := GroupModel β

def word (p : ℕ) (g h : Q β) : Q β := h*g*h⁻¹*(g^p)⁻¹

theorem pow_four (g : Q β) : g^4=1 := by
  change g^(2*2)=1
  rw [pow_mul,GroupModel.square_coordinates,GroupModel.square_coordinates]
  apply GroupModel.ext <;> simp

theorem word_one (g h : Q β) :
    word β 1 g h=(⟨0,β g.base h.base-β h.base g.base⟩ : Q β) := by
  have hn (w : W) : -w=w := by
    apply neg_eq_iff_add_eq_zero.mpr
    exact GroupModel.add_self_of_charTwo (R := ZMod 2) w
  have he := GroupModel.commutator_coordinates β h⁻¹ g⁻¹
  simp only [inv_inv] at he
  change h*g*h⁻¹*(g^1)⁻¹=_
  rw [pow_one,he]
  apply GroupModel.ext
  · rfl
  · simp only [GroupModel.inv_base,map_neg,LinearMap.neg_apply,neg_neg,sub_eq_add_neg,hn]
    abel

theorem word_three (g h : Q β) :
    word β 3 g h=(⟨0,β g.base h.base-β h.base g.base+β g.base g.base⟩ : Q β) := by
  have hg : g^3=g⁻¹ := eq_inv_iff_mul_eq_one.mpr (by rw [← pow_succ]; exact pow_four β g)
  change h*g*h⁻¹*(g^3)⁻¹=_
  rw [hg,inv_inv]
  calc
    h*g*h⁻¹*g=word β 1 g h*g^2 := by
      simp only [word,pow_one,pow_two,mul_assoc,inv_mul_cancel_left]
    _ = (⟨0,β g.base h.base-β h.base g.base⟩ : Q β)*⟨0,β g.base g.base⟩ := by
      rw [word_one,GroupModel.square_coordinates]
    _ = _ := by ext <;> simp

/-- Literal tame relators have the expected square/commutator coordinate for every odd exponent. -/
theorem word_odd (p : ℕ) (hp : p%4=1 ∨ p%4=3) (g h : Q β) :
    word β p g h=(⟨0,β g.base h.base-β h.base g.base+
      (if p%4=3 then 1 else 0 : ZMod 2) • β g.base g.base⟩ : Q β) := by
  have hm : word β p g h=word β (p%4) g h := by
    unfold word
    rw [pow_eq_pow_mod p (pow_four β g)]
  rw [hm]
  rcases hp with hp | hp
  · rw [hp,word_one]
    simp
  · rw [hp,word_three]
    simp

end UnitDistance.ClassTwo.Tame
