module

public import UnitDistance.PadicTwoSquareclasses

@[expose] public section
set_option backward.privateInPublic true


/-! Four genuine unit squareclasses bound every exponent-two image. -/
noncomputable section
namespace UnitDistance.PadicTwo
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem unit_squareclass_units (u : ℤ_[2]ˣ) :
    ∃ (i : Fin 4) (z : ℤ_[2]ˣ),u=representativeUnit i*z^2 := by
  obtain ⟨i,z,hz⟩ := unit_squareclass u
  have hzu : IsUnit z := by
    have hh : IsUnit ((unitRepresentative i : ℤ_[2])*z^2) := hz ▸ u.isUnit
    exact (isUnit_pow_iff (by decide : 2≠0)).mp ((Commute.all _ _).isUnit_mul_iff.mp hh).2
  refine ⟨i,hzu.unit,?_⟩
  apply Units.ext
  simpa only [Units.val_mul,Units.val_pow_eq_pow_val,representativeUnit_val,hzu.unit_spec] using hz

variable {H : Type*} [Group H]

/-- No exponent-two homomorphic image of the actual Q₂ integer units has more than four elements. -/
theorem unit_image_card_le_four (f : ℤ_[2]ˣ →* H) (hf : ∀ u,f u^2=1) :
    Nat.card f.range≤4 := by
  let r : Fin 4 → f.range := fun i => ⟨f (representativeUnit i),⟨representativeUnit i,rfl⟩⟩
  have hr : Function.Surjective r := by
    rintro ⟨h,⟨u,rfl⟩⟩
    obtain ⟨i,z,rfl⟩ := unit_squareclass_units u
    refine ⟨i,?_⟩
    apply Subtype.ext
    simp [r,map_mul,map_pow,hf]
  simpa using Nat.card_le_card_of_surjective r hr

end UnitDistance.PadicTwo
