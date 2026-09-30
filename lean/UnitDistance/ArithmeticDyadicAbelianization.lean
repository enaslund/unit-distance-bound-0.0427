module

public import UnitDistance.ArithmeticDyadicModel
public import UnitDistance.DyadicAbelianization
public import UnitDistance.PadicTwoUnitImages

@[expose] public section
set_option backward.privateInPublic true


/-! Actual dyadic group invariants and the numerical consequence of genuine
unit reciprocity and residue maps. -/
noncomputable section
namespace UnitDistance.ArithmeticDyadic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem abelianization_card : Nat.card (Abelianization G)=16 := by
  rw [← Nat.card_congr galoisEquiv.abelianizationCongr.toEquiv]
  exact Dyadic.D.abelianization_card

theorem exponent_four (g : G) : g^4=1 := by
  obtain ⟨d,rfl⟩ := galoisEquiv.surjective g
  rw [← map_pow,Dyadic.D.exponent_four,map_one]

/-- Any actual cyclic residue action and unit reciprocity with their true
index identity determine residue degree four and inertia order eight. -/
theorem residue_inertia_cards {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (r : G →* A) (hr : Function.Surjective r)
    (u : ℤ_[2]ˣ →* Abelianization G) (hu : ∀ a,u a^2=1)
    (hindex : u.range.index=Nat.card A) : Nat.card A=4 ∧ Nat.card r.ker=8 := by
  have hpow : ∀ a : A,a^4=1 := by
    intro a
    obtain ⟨g,rfl⟩ := hr a
    rw [← map_pow,exponent_four,map_one]
  have hdiv : Nat.card A∣4 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  have hA : Nat.card A≤4 := Nat.le_of_dvd (by decide) hdiv
  have hu4 := PadicTwo.unit_image_card_le_four u hu
  have hc := u.range.card_mul_index
  rw [hindex,abelianization_card] at hc
  have hA4 : Nat.card A=4 := by nlinarith
  refine ⟨hA4,?_⟩
  have hcG := r.ker.card_mul_index
  rw [Subgroup.index_ker,r.range_eq_top_of_surjective hr,Subgroup.card_top,galoisGroup_card,hA4] at hcG
  omega

end UnitDistance.ArithmeticDyadic
