module

public import UnitDistance.Target

@[expose] public section
set_option backward.privateInPublic true


/-!
# The planar target at exponent `1.04315`

Same counting as `UnitDistance.Target` (`unitPairs` divides the ordered
unit-distance pairs by two); only the exponent changes. `increment` is the
exponent gain δ = 0.04315 of the 41-cap tower over `ℚ(√241)`.
-/

open Filter

namespace UnitDistance.Sqrt241

noncomputable def increment : ℝ := 863 / 20000

noncomputable def exponent : ℝ := 20863 / 20000

theorem exponent_eq : exponent = 1 + increment := by
  norm_num [exponent, increment]

theorem increment_pos : 0 < increment := by norm_num [increment]

theorem increment_lt_one : increment < 1 := by norm_num [increment]

/-- The planar statement at exponent `20863/20000`. No theorem in this file proves it. -/
def Target : Prop :=
  ∃ U : ℕ → Finset ℂ,
    Tendsto (fun j => (U j).card) atTop atTop ∧
    Tendsto (fun j => UnitDistance.unitPairs (U j) / ((U j).card : ℝ) ^ exponent)
      atTop atTop

end UnitDistance.Sqrt241
