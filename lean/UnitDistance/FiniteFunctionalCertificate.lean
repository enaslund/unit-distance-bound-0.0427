module

public import UnitDistance.FiniteFunctionalArithmetic
public import UnitDistance.FiniteCertificates.All
public import UnitDistance.NumericalReduction

@[expose] public section
set_option backward.privateInPublic true


/-! # Certified finite-place profit and the remaining pair-integral input

Every real-power and logarithm enclosure used here is separately proved.
The final finite-profit lower bound concerns the independently defined actual
witness. The margin theorem has only the actual pair-functional enclosure as
its remaining numerical hypothesis; no field-tower conclusion is claimed.
-/

noncomputable section
open scoped BigOperators

namespace UnitDistance.Witness
open FiniteCertificates

/-- A lower enclosure assembled from the proved bounds with the coefficient
signs required by the actual logarithmic functional. -/
def finiteFunctionalLower (v : Fin 11) : ℝ :=
  -increment * periodPower v * residueLogUpper v + energyLogLower v -
    2 * (1 + increment) * massLogUpper v

theorem finiteLp_le_massUpper (v : Fin 11) : finiteLp v ≤ massUpper v :=
  finiteLp_le_massUpper_of_power_bounds v (power_bounds v)

theorem finiteLogFunctional_lower (v : Fin 11) :
    finiteFunctionalLower v ≤ finiteLogFunctional v :=
  finiteLogFunctional_lower_of_bounds v (power_bounds v)
    (residue_log_upper v) (energy_log_lower v) (mass_log_upper v)

/-- The full lower rational sum, before rounding to the certificate threshold. -/
theorem finiteProfit_explicit_lower :
    (66148283040255179604979809 : ℝ) / 64000000000000000000000000 ≤ finiteProfit := by
  calc
    _ = ∑ v : Fin 11, finiteFunctionalLower v / (ramification v * residueDegree v) := by
      norm_num [finiteFunctionalLower, increment, periodPower, residueLogUpper,
        energyLogLower, massLogUpper, ramification, residueDegree,
        Fin.sum_univ_succ, Matrix.cons_val]
    _ ≤ finiteProfit := by
      apply Finset.sum_le_sum
      intro v _
      exact div_le_div_of_nonneg_right (finiteLogFunctional_lower v) (by positivity)

/-- Unconditional evaluation of the actual finite-place witness functional. -/
theorem finiteProfit_lower : (1033566922503 : ℝ) / 10^12 ≤ finiteProfit := by
  linarith [finiteProfit_explicit_lower]

/-- Only the actual two-complex-coordinate integral enclosure remains in the
numerical input ledger. Structural tower and analytic-family inputs are
separate from this theorem. -/
theorem numericalBounds_of_pair
    (hpair : (1379635324335 : ℝ) / 10^12 ≤ JPair) : NumericalBounds :=
  numericalBounds_of_pair_finite hpair finiteProfit_lower

theorem uniform_margin_of_pair
    (hpair : (1379635324335 : ℝ) / 10^12 ≤ JPair)
    {θ : ℝ} (hθ : thetaMin ≤ θ) :
    (533 : ℝ) / 10^8 < margin θ - 4 * epsilon :=
  uniform_margin_of_pair_finite hpair finiteProfit_lower hθ

end UnitDistance.Witness
