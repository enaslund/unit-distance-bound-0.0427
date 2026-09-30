module

public import UnitDistance.ArithmeticDyadicIntrinsic
public import UnitDistance.LocalInertiaFiniteImage

@[expose] public section
set_option backward.privateInPublic true


/-! Exact inertia and residue degrees of the actual retained dyadic field,
from actual local reciprocity and the proved integral-unit squareclasses. -/
noncomputable section
open scoped ValuativeRel
namespace UnitDistance.ArithmeticDyadic
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory
local instance inertiaCardsInstance1 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance inertiaCardsInstance2 : NontriviallyNormedField LocalField := intrinsicNormedField
local instance inertiaCardsInstance3 : ValuativeRel LocalField := intrinsicValuativeRel
local instance inertiaCardsInstance4 : IsNonarchimedeanLocalField LocalField := intrinsicLocalField
local instance inertiaCardsInstance5 : Valuation.HasExtension (ValuativeRel.valuation ℚ_[2])
    (ValuativeRel.valuation LocalField) := intrinsicHasExtension
local instance inertiaCardsInstance6 : IsIntegralClosure 𝒪[LocalField] 𝒪[ℚ_[2]] LocalField := intrinsicIntegralClosure

/-- Every actual dyadic integer-unit Artin image has order dividing two. -/
theorem intrinsicUnitArtin_square (u : ℤ_[2]ˣ) : intrinsicUnitArtin u ^ 2 = 1 := by
  have h := ArithmeticProP.localArtin_integerUnit_mem_residueInertia_image
    ℚ_[2] LocalField (intrinsicUnitEquiv u)
  obtain ⟨σ,hσ,himage⟩ := h
  change Abelianization.of σ = intrinsicUnitArtin u at himage
  rw [←himage,←map_pow,intrinsicInertia_square ⟨σ,hσ⟩,map_one]

/-- The actual retained dyadic extension has residue degree four and inertia order eight. -/
theorem actual_residueDegree_inertia_card :
    intrinsicResidueDegree = 4 ∧ Nat.card inertia = 8 :=
  inertia_card_of_unit_image_exponent_two intrinsicUnitArtin_square

end UnitDistance.ArithmeticDyadic
