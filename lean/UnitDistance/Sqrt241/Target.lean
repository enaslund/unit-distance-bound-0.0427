module

public import UnitDistance.Target

@[expose] public section
set_option backward.privateInPublic true


/-!
# The planar target at exponent `1.0427`

Same counting as `UnitDistance.Target` (`unitPairs` divides the ordered
unit-distance pairs by two); only the exponent changes. `increment` is the
exponent gain δ = 0.0427 of the tower over `ℚ(√241)`.
-/

open Filter

namespace UnitDistance.Sqrt241

noncomputable def increment : ℝ := 427 / 10000

noncomputable def exponent : ℝ := 10427 / 10000

theorem exponent_eq : exponent = 1 + increment := by
  norm_num [exponent, increment]

theorem increment_pos : 0 < increment := by norm_num [increment]

theorem increment_lt_one : increment < 1 := by norm_num [increment]

/-- The planar statement at exponent `10427/10000`. No theorem in this file proves it. -/
def Target : Prop :=
  ∃ U : ℕ → Finset ℂ,
    Tendsto (fun j => (U j).card) atTop atTop ∧
    Tendsto (fun j => UnitDistance.unitPairs (U j) / ((U j).card : ℝ) ^ exponent)
      atTop atTop

end UnitDistance.Sqrt241
