module

public import UnitDistance.NumericalReduction

@[expose] public section
set_option backward.privateInPublic true


/-! The actual finite witness period satisfies the uniform Fourier separation
criterion. Only crude proved logarithm bounds are needed for its large margin. -/

noncomputable section
open scoped BigOperators
namespace UnitDistance.Witness

/-- Normalized logarithmic volume of the actual published finite periods. -/
def periodLogDensity : ℝ :=
  ∑ v : Fin 11, (periodPower v : ℝ)*Real.log (primes v)/(ramification v : ℝ)

theorem periodLogDensity_lower : (24 : ℝ) ≤ periodLogDensity := by
  let q : Fin 11 → ℕ := ![1, 1, 2, 2, 3, 3, 4, 4, 4, 4, 4]
  have hp (v : Fin 11) : (2 : ℝ)^(q v) ≤ primes v := by
    fin_cases v <;> norm_num [q, primes]
  have hl (v : Fin 11) : (q v : ℝ)*Real.log 2 ≤ Real.log (primes v) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (hp v)
  have h2 : (2/3 : ℝ) ≤ Real.log 2 := by
    have h := log_two_precise.1
    norm_num only [div_one] at h
    linarith
  calc
    (24 : ℝ) ≤ (303/8 : ℝ)*Real.log 2 := by linarith
    _ = ∑ v : Fin 11, (periodPower v : ℝ)*((q v : ℝ)*Real.log 2)/(ramification v : ℝ) := by
      norm_num [periodPower, ramification, q, Fin.sum_univ_succ]
      ring
    _ ≤ periodLogDensity := by
      apply Finset.sum_le_sum
      intro v _
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hl v) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem logRD_le_seven : logRD ≤ 7 := by
  have h2 := log_two_precise.2
  norm_num only [div_one] at h2
  have hD := log_discriminant_upper
  unfold logRD
  linarith

/-- The exact published finite periods satisfy the scalar condition with
the proved common Fourier constants `M = 2`, `sigma = 1`. -/
theorem period_fourier_separation :
    Real.log 2+2*Real.log 5+2 ≤ 2*Real.exp (periodLogDensity/2-logRD) := by
  have hx : 5 ≤ periodLogDensity/2-logRD := by
    linarith [periodLogDensity_lower, logRD_le_seven]
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have h5 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<5)
  have he := Real.add_one_le_exp (periodLogDensity/2-logRD)
  linarith

end UnitDistance.Witness
