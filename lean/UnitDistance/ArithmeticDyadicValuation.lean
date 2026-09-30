module

public import UnitDistance.ArithmeticDyadicInertia
public import UnitDistance.PadicFiniteGaloisValuation

@[expose] public section
set_option backward.privateInPublic true


/-! The actual complete valuation and actual inertia of the retained Q₂ base change. -/
noncomputable section
namespace UnitDistance.ArithmeticDyadic
open RamificationTheory.HilbertRamification.Higher
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev localBaseValuation := PadicFiniteGalois.base 2
abbrev localValuation := PadicFiniteGalois.target 2 LocalField
theorem localUnique : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
    localBaseValuation.toDVF localValuation.toDVF :=
  OddTame.completeUnique localBaseValuation localValuation

def inertia : Subgroup G := lowerRamificationGroup
  (base:=localBaseValuation.toDVF) (target:=localValuation.toDVF) localUnique ((0 : ℕ) : ℝ)

theorem residue_two : (2 : localValuation.residueField)=0 := by
  have h : (2 : ZMod 2)=0 := by decide
  have he := congrArg (PadicFiniteGalois.residueEmbedding 2 LocalField) h
  simpa only [map_ofNat,map_zero] using he

/-- The true inertia of the actual degree32 local field has exponent two. -/
theorem actual_inertia_square (σ : inertia) : (σ : G)^2=1 :=
  inertia_square localUnique residue_two σ

/-- The true inertia of the actual degree32 local field is abelian. -/
theorem actual_inertia_commute (σ τ : inertia) : (σ : G)*(τ : G)=(τ : G)*(σ : G) :=
  inertia_commute localUnique residue_two σ τ

end UnitDistance.ArithmeticDyadic
