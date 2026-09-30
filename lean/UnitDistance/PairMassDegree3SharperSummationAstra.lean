module

public import UnitDistance.PairMassDegree3SummationCertificate

@[expose] public section
set_option backward.privateInPublic true


/-! The exact rational value of the degree-3 outward sum and a sharper
mass endpoint. This is kept separate from the certificate used by the wide
final target so it can be reused without changing that integration path. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace UnitDistance.Witness

/-- Exact value of the 64-cell rational outward sum. -/
theorem pairMass_outward_sum3_exact :
    (∑ i : Fin 8, ∑ j : Fin 8,
      pairMassContractionUpper3 i j * pairMassCenterPowerUpper i j) =
      (77937724053617020685714880552767926909 : ℝ) /
        2000000000000000000000000000000000000 := by
  norm_num [pairMassContractionUpper3, pairMassCenterPowerUpper,
    Fin.sum_univ_succ]

/-- Convenient six-decimal enclosure of the exact outward sum. -/
theorem pairMass_outward_sum3_lt_38968863 :
    (∑ i : Fin 8, ∑ j : Fin 8,
      pairMassContractionUpper3 i j * pairMassCenterPowerUpper i j) <
      (38968863 : ℝ) / 1000000 := by
  rw [pairMass_outward_sum3_exact]
  norm_num

/-- The cell contraction hypotheses imply the exact rational outward sum. -/
theorem pairMassBetaIntegral_le_of_degree3_contraction_bounds_exact
    (hc : ∀ i j, pairMassCellContraction3 i j ≤ pairMassContractionUpper3 i j) :
    pairMassBetaIntegral ≤
      (77937724053617020685714880552767926909 : ℝ) /
        2000000000000000000000000000000000000 := by
  rw [pairMassBetaIntegral_eq_sum_cells]
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
    pairMass_outward_sum3_exact.le
  exact (pairMass_cell_integral_le3 i j).trans
    (mul_le_mul (hc i j) (pairMassCellCenter_power_le i j)
      (Real.rpow_nonneg (pairMassCellCenter_pos i j).le p)
      (pairMassContractionUpper3_nonneg i j))

/-- The degree-3 contraction bounds imply the sharper mass endpoint
`38.968863`. -/
theorem pairMassBetaIntegral_le_of_degree3_contraction_bounds_sharper
    (hc : ∀ i j, pairMassCellContraction3 i j ≤ pairMassContractionUpper3 i j) :
    pairMassBetaIntegral ≤ (38968863 : ℝ) / 1000000 := by
  have h := pairMass_outward_sum3_lt_38968863
  rw [pairMass_outward_sum3_exact] at h
  exact (pairMassBetaIntegral_le_of_degree3_contraction_bounds_exact hc).trans h.le

end UnitDistance.Witness
