module

public import UnitDistance.Sqrt241.FiniteFunctionalArithmetic
public import UnitDistance.Sqrt241.FiniteCertificates.All

@[expose] public section
set_option backward.privateInPublic true


/-! # Certified finite-place profit of the witness over `ℚ(√241)`

Port of the finite-profit part of `UnitDistance.FiniteFunctionalCertificate`.
Every real-power and logarithm enclosure used here is proved in the generated
certificate modules; the conclusion is a lower bound for the finite-place
functional `finiteProfit` of `UnitDistance.Sqrt241.Witness` at δ = 0.04315.
-/

noncomputable section
open scoped BigOperators

namespace UnitDistance.Sqrt241.Witness
open FiniteCertificates

/-- A lower enclosure assembled from the proved bounds with the coefficient
signs required by the logarithmic functional. -/
def finiteFunctionalLower (v : Fin 5) : ℝ :=
  -increment * periodPower v * residueLogUpper v + energyLogLower v -
    2 * (1 + increment) * massLogUpper v

theorem finiteLp_le_massUpper (v : Fin 5) : finiteLp v ≤ massUpper v :=
  finiteLp_le_massUpper_of_power_bounds v (power_bounds v)

theorem finiteLogFunctional_lower (v : Fin 5) :
    finiteFunctionalLower v ≤ finiteLogFunctional v :=
  finiteLogFunctional_lower_of_bounds v (power_bounds v)
    (residue_log_upper v) (energy_log_lower v) (mass_log_upper v)

/-- The full lower rational sum, before rounding. -/
theorem finiteProfit_explicit_lower :
    (459906351912729240389471 : ℝ) / 640000000000000000000000 ≤ finiteProfit := by
  calc
    _ = ∑ v : Fin 5, finiteFunctionalLower v / (ramification v * residueDegree v) := by
      norm_num [finiteFunctionalLower, increment, periodPower, residueLogUpper,
        energyLogLower, massLogUpper, ramification, residueDegree,
        Fin.sum_univ_succ, Matrix.cons_val]
    _ ≤ finiteProfit := by
      apply Finset.sum_le_sum
      intro v _
      exact div_le_div_of_nonneg_right (finiteLogFunctional_lower v) (by positivity)

/-- Evaluation of the finite-place witness functional at δ = 0.04315. -/
theorem finiteProfit_lower : (718603674 : ℝ) / 10^9 ≤ finiteProfit := by
  linarith [finiteProfit_explicit_lower]

end UnitDistance.Sqrt241.Witness
