module

public import UnitDistance.TensorOverlapLaw

@[expose] public section
set_option backward.privateInPublic true


/-! Exact logarithmic normalization of the actual Gaussian/Student tensor
profile functional. All masses are the literal ordinary-volume integrals. -/

noncomputable section
open scoped Classical
namespace UnitDistance.Witness

variable (β γ : Type*) [Fintype β] [Fintype γ]

/-- The actual tensor overlap divided by its actual p-mass power. -/
def tensorFunctional : ℝ :=
  tensorOverlapMass β γ / (compactMass^Fintype.card β*pairMass^Fintype.card γ)^(1+increment)

theorem tensorFunctional_pos : 0 < tensorFunctional β γ := by
  unfold tensorFunctional
  exact div_pos (tensorOverlapMass_pos (β := β) (γ := γ))
    (Real.rpow_pos_of_pos (by positivity [compactMass_pos, pairMass_pos]) _)

/-- The tensor functional is exactly the exponential of the sum of the
literal local logarithmic functionals. -/
theorem tensorFunctional_eq_exp :
    tensorFunctional β γ =
      Real.exp ((Fintype.card β : ℝ)*JCompact+(Fintype.card γ : ℝ)*JPair) := by
  have hA : 0 < compactMass^Fintype.card β*pairMass^Fintype.card γ := by
    positivity [compactMass_pos, pairMass_pos]
  have hZ := tensorOverlapMass_pos (β := β) (γ := γ)
  rw [tensorFunctional, Real.rpow_def_of_pos hA, ← Real.exp_log hZ, ← Real.exp_sub]
  congr 1
  rw [tensorOverlapMass, Real.log_mul (pow_pos compactOverlap_pos _).ne'
      (pow_pos pairOverlap_pos _).ne',
    Real.log_mul (pow_pos compactMass_pos _).ne' (pow_pos pairMass_pos _).ne']
  simp only [Real.log_pow, JCompact, JPair]
  ring

/-- No tensor integral remains hidden in the logarithmic functional. -/
theorem log_tensorFunctional :
    Real.log (tensorFunctional β γ) =
      (Fintype.card β : ℝ)*JCompact+(Fintype.card γ : ℝ)*JPair := by
  rw [tensorFunctional_eq_exp, Real.log_exp]

end UnitDistance.Witness
