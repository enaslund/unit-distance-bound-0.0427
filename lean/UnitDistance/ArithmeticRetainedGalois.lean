module

public import UnitDistance.ArithmeticRetainedField
public import UnitDistance.ArithmeticCompletedField
public import UnitDistance.GeneratedQuadraticExponent
public import Mathlib.GroupTheory.PGroup

@[expose] public section
set_option backward.privateInPublic true


/-! Proved exponent and central-kernel properties of the actual finite
retained and completed Galois groups. -/
noncomputable section
namespace UnitDistance.ArithmeticRetained
open ArithmeticChosenGenus Multiquadratic

theorem retained_aut_pow_four : ∀ σ : Gal(RetainedField/ℚ), σ^4=1 := by
  rw [← retainedTower_baseAlgebra_eq]
  exact fullRetainedTower.aut_pow_four every_automorphism_involutive

theorem retained_relative_aut_square : ∀ σ : Gal(RetainedField/ℚ),
    (∀ x : GenusField, σ (algebraMap GenusField RetainedField x)=
      algebraMap GenusField RetainedField x) → σ^2=1 := by
  rw [← retainedTower_baseAlgebra_eq]
  exact fullRetainedTower.aut_sq_eq_one

theorem retained_relative_aut_central : ∀ σ τ : Gal(RetainedField/ℚ),
    (∀ x : GenusField, σ (algebraMap GenusField RetainedField x)=
      algebraMap GenusField RetainedField x) → Commute σ τ := by
  rw [← retainedTower_baseAlgebra_eq]
  exact fullRetainedTower.aut_commute (fun i _ => retainedRadicand_invariant i)

theorem retained_aut_square_central : ∀ σ τ : Gal(RetainedField/ℚ), Commute (σ^2) τ := by
  rw [← retainedTower_baseAlgebra_eq]
  exact fullRetainedTower.aut_square_commute every_automorphism_involutive
    (fun i _ => retainedRadicand_invariant i)

theorem retained_isPGroup : IsPGroup 2 (Gal(RetainedField/ℚ)) :=
  IsPGroup.of_card (n := 19) retainedField_galoisGroup_card

end UnitDistance.ArithmeticRetained
namespace UnitDistance.ArithmeticCompleted
open ArithmeticChosenGenus Multiquadratic

theorem completed_aut_pow_four : ∀ σ : Gal(CompletedField/ℚ), σ^4=1 := by
  rw [← completedTower_baseAlgebra_eq]
  exact completedTower.aut_pow_four every_automorphism_involutive

theorem completed_relative_aut_central : ∀ σ τ : Gal(CompletedField/ℚ),
    (∀ x : GenusField, σ (algebraMap GenusField CompletedField x)=
      algebraMap GenusField CompletedField x) → Commute σ τ := by
  rw [← completedTower_baseAlgebra_eq]
  exact completedTower.aut_commute (fun i _ => completedRadicand_invariant i)

theorem completed_isPGroup : IsPGroup 2 (Gal(CompletedField/ℚ)) :=
  IsPGroup.of_card (n := 14) completedField_galoisGroup_card

end UnitDistance.ArithmeticCompleted
