module

public import UnitDistance.ArithmeticDyadicModel
public import UnitDistance.DyadicInertiaRadical

@[expose] public section
set_option backward.privateInPublic true


/-! Actual dyadic inertia lies in the elementary abelian subgroup fixed by
sqrt5. Identifying its precise order requires a further unramified-field
calculation; no inertia cardinality is assumed here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticDyadic
open Multiquadratic ClassTwo
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem localBase_square_zero : ∀ v : Fin 3 → ZMod 2,
    v 2=0 → RetainedQuadratic.cocycle (localBase v) (localBase v)=0 := by
  decide +kernel

private theorem localBase_symmetric : ∀ v w : Fin 3 → ZMod 2,
    v 2=0 → w 2=0 → RetainedQuadratic.cocycle (localBase v) (localBase w)=
      RetainedQuadratic.cocycle (localBase w) (localBase v) := by decide +kernel

attribute [local irreducible] RetainedQuadratic.cocycle

theorem sq_eq_one_of_fixes_five (σ : G) (hσ : σ (genusRoot 3)=genusRoot 3) : σ^2=1 := by
  have hz : (signMap σ).toAdd 2=0 := by
    apply binarySign_injective (E:=LocalField)
    rw [binarySign_zero]
    apply mul_right_cancel₀ (genusRoot_ne_zero 3)
    change binarySign ((model σ).base 3)*genusRoot 3=1*genusRoot 3
    rw [← genusRoot_action,hσ,one_mul]
  apply model_injective
  rw [map_pow,map_one,GroupModel.square_coordinates,model_base_shape,
    localBase_square_zero _ hz]
  rfl

theorem commute_of_fixes_five (σ τ : G)
    (hσ : σ (genusRoot 3)=genusRoot 3) (hτ : τ (genusRoot 3)=genusRoot 3) :
    σ*τ=τ*σ := by
  have hz (g : G) (hg : g (genusRoot 3)=genusRoot 3) : (signMap g).toAdd 2=0 := by
    apply binarySign_injective (E:=LocalField)
    rw [binarySign_zero]
    apply mul_right_cancel₀ (genusRoot_ne_zero 3)
    change binarySign ((model g).base 3)*genusRoot 3=1*genusRoot 3
    rw [← genusRoot_action,hg,one_mul]
  apply model_injective
  rw [map_mul,map_mul]
  apply GroupModel.ext
  · simp [add_comm]
  · simp only [GroupModel.mul_central,model_base_shape]
    rw [localBase_symmetric _ _ (hz σ hσ) (hz τ hτ)]
    abel

variable {base : DVF.{0,0} ℚ_[2]} {target : DVF.{0,0} LocalField}
  [base.valuation.HasExtension target.valuation]
  (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
    base target)
  (h2 : (2 : target.residueField)=0)

include h2

/-- Every member of actual valuation-theoretic inertia has order at most two. -/
theorem inertia_square (σ : lowerRamificationGroup (base:=base) (target:=target)
    huniq ((0 : ℕ) : ℝ)) : (σ : G)^2=1 := by
  apply sq_eq_one_of_fixes_five
  apply DyadicInertia.inertia_fixes_sqrt_five huniq h2 σ
  have h := genusRoot_sq 3
  norm_num [ArithmeticChosenGenus.radicands] at h ⊢
  exact h

/-- The actual dyadic inertia group is abelian. -/
theorem inertia_commute (σ τ : lowerRamificationGroup (base:=base) (target:=target)
    huniq ((0 : ℕ) : ℝ)) : (σ : G)*(τ : G)=(τ : G)*(σ : G) := by
  apply commute_of_fixes_five
  all_goals
    apply DyadicInertia.inertia_fixes_sqrt_five huniq h2
    have h := genusRoot_sq 3
    norm_num [ArithmeticChosenGenus.radicands] at h ⊢
    exact h

end UnitDistance.ArithmeticDyadic
