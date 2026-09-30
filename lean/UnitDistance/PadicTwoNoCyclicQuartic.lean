module

public import UnitDistance.CyclicQuarticNorm
public import UnitDistance.PadicTwoImaginaryNorm

@[expose] public section
set_option backward.privateInPublic true


/-! No actual cyclic quartic extension of Q₂ contains a square root of minus one. -/
noncomputable section
namespace UnitDistance.PadicTwo
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The imaginary quadratic character of Q₂ has no cyclic quartic lift. -/
theorem no_cyclic_quartic (L : Type*) [Field L] [Algebra ℚ_[2] L]
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L] [IsCyclic Gal(L/ℚ_[2])]
    (hd : Module.finrank ℚ_[2] L=4) (i : L) (hi : i^2= -1) : False := by
  obtain ⟨E,iE,hiE,hE,z,hz⟩ := CyclicQuartic.exists_quadratic_norm_neg_one hd i hi
  exact quadratic_norm_ne_neg_one iE hiE hE z hz

end UnitDistance.PadicTwo
