/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.35 Mathlib now supplies the
formal log/exp composition proofs in Mathlib.RingTheory.PowerSeries.Log.
Original downstream declaration names and mathematical statements are retained.
-/

module

public import Mathlib.RingTheory.PowerSeries.Log

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Formal logarithm and exponential composition

Mathlib now proves both composition identities directly. These two declarations
keep the source names used by the local-field development.
-/

noncomputable section

namespace PowerSeries

/-- Substituting the formal logarithm into the exponential yields `1 + X`. -/
theorem exp_subst_log_eq_one_add_X
    (A : Type*) [CommRing A] [Algebra ℚ A] [IsAddTorsionFree A] :
    PowerSeries.subst (PowerSeries.log A) (PowerSeries.exp A) =
      (1 + PowerSeries.X : PowerSeries A) := by
  exact PowerSeries.subst_exp_log A

/-- Substituting `exp - 1` into the formal logarithm yields `X`. -/
theorem log_subst_exp_sub_one_eq_X
    (A : Type*) [CommRing A] [Algebra ℚ A] [IsAddTorsionFree A] :
    PowerSeries.subst ((PowerSeries.exp A) - 1) (PowerSeries.log A) =
      (PowerSeries.X : PowerSeries A) := by
  exact PowerSeries.subst_log_exp_sub_one A

end PowerSeries
