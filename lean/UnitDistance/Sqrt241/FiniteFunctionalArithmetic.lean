module

public import UnitDistance.Sqrt241.FiniteCertificates.Data

@[expose] public section
set_option backward.privateInPublic true


/-! # Exact rational comparisons for the finite-place witness over ℚ(√241)

Port of `UnitDistance.FiniteFunctionalArithmetic` to `UnitDistance.Sqrt241.Witness`.

The rational candidate tables are linked to the independently defined shell
weights, masses, energy and real-power functional in `Witness.lean`.
-/

noncomputable section
open scoped BigOperators

namespace UnitDistance.Sqrt241.Witness
open FiniteCertificates

theorem residueCard_gt_one (v : Fin 5) : 1 < residueCard v := by
  fin_cases v <;> norm_num [residueCard, primes, residueDegree]

theorem shellMass_pos (v : Fin 5) (i : ℕ) : 0 < Local.shellMass (residueCard v) i := by
  have hq := residueCard_gt_one v
  cases i with
  | zero => norm_num [Local.shellMass]
  | succ i =>
    simp only [Local.shellMass, pow_succ]
    have hi := pow_pos (lt_trans zero_lt_one hq) i
    nlinarith

theorem finiteLp_pos (v : Fin 5) : 0 < finiteLp v := by
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (shellMass_pos v i)
      (Real.rpow_pos_of_pos (by exact_mod_cast shellWeights_pos v i) _)
  · exact Finset.univ_nonempty

/-- Exact arithmetic checks the upper mass table against the weighted sum of
the separate real-power upper bounds. -/
theorem powerUpper_mass_le (v : Fin 5) :
    ∑ i : Fin 6, Local.shellMass (residueCard v) i * powerUpper v i ≤ massUpper v := by
  fin_cases v <;>
    norm_num [powerUpper, massUpper, residueCard, primes, residueDegree,
      Local.shellMass, Fin.sum_univ_succ, Matrix.cons_val]

theorem finiteLp_le_massUpper_of_power_bounds (v : Fin 5)
    (hpow : ∀ i : Fin 6, (shellWeights v i : ℝ) ^ p ≤ powerUpper v i) :
    finiteLp v ≤ massUpper v := by
  apply le_trans _ (powerUpper_mass_le v)
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpow i) (shellMass_pos v i).le

set_option maxHeartbeats 4000000 in
/-- Exact arithmetic checks the lower table against the actual rational
second moment and transition form, including all off-diagonal shell terms. -/
theorem energyLower_le (v : Fin 5) :
    energyLower v ≤ ((periodPower v : ℝ) + 1) * finiteSecond v ^ 2 +
      2 * finiteSecond v * finiteTransition v := by
  fin_cases v <;>
    norm_num [energyLower, periodPower, finiteSecond, finiteTransition,
      shellWeights, residueCard, primes, residueDegree, Local.shellMass,
      Local.shellD, Fin.sum_univ_succ, Matrix.cons_val]

theorem energyLower_pos (v : Fin 5) : 0 < energyLower v := by
  fin_cases v <;> norm_num [energyLower]

theorem finiteLogFunctional_lower_of_bounds (v : Fin 5)
    {qUpper eLower mUpper : ℝ}
    (hpow : ∀ i : Fin 6, (shellWeights v i : ℝ) ^ p ≤ powerUpper v i)
    (hq : Real.log (residueCard v) ≤ qUpper)
    (he : eLower ≤ Real.log (energyLower v))
    (hm : Real.log (massUpper v) ≤ mUpper) :
    -increment * periodPower v * qUpper + eLower - 2 * (1 + increment) * mUpper ≤
      finiteLogFunctional v := by
  have he' := he.trans (Real.log_le_log (energyLower_pos v) (energyLower_le v))
  have hm' := (Real.log_le_log (finiteLp_pos v)
    (finiteLp_le_massUpper_of_power_bounds v hpow)).trans hm
  have hq' := mul_le_mul_of_nonneg_left hq
    (mul_nonneg increment_pos.le (Nat.cast_nonneg (periodPower v)))
  have hm'' := mul_le_mul_of_nonneg_left hm'
    (show 0 ≤ 2 * (1 + increment) by linarith [increment_pos])
  unfold finiteLogFunctional
  linarith

end UnitDistance.Sqrt241.Witness
