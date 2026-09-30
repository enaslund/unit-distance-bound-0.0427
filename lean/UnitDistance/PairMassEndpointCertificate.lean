module

public import UnitDistance.PairMassDegree12Data

@[expose] public section
set_option backward.privateInPublic true


/-! Kernel-checked fifth-power enclosures for the nine beta-moment endpoints. -/

noncomputable section
namespace UnitDistance.Witness

private theorem six_fifths_rpow_fifth {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (6 / 5 : ℝ)) ^ (5 : ℕ) = x ^ (6 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private theorem lower_le_six_fifths_rpow {x l : ℝ} (hx : 0 ≤ x) (hl : 0 ≤ l)
    (hpow : l ^ (5 : ℕ) ≤ x ^ (6 : ℕ)) : l ≤ x ^ (6 / 5 : ℝ) := by
  rw [← pow_le_pow_iff_left₀ hl (Real.rpow_nonneg hx _)
    (by norm_num : (5 : ℕ) ≠ 0)]
  rw [six_fifths_rpow_fifth hx]
  exact hpow

private theorem six_fifths_rpow_le_upper {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u)
    (hpow : x ^ (6 : ℕ) ≤ u ^ (5 : ℕ)) : x ^ (6 / 5 : ℝ) ≤ u := by
  rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg hx _) hu
    (by norm_num : (5 : ℕ) ≠ 0)]
  rw [six_fifths_rpow_fifth hx]
  exact hpow

theorem pairMassEndpointLower_le (k : Fin 9) :
    pairMassEndpointLower k ≤ pairMassEndpointRoot k := by
  unfold pairMassEndpointRoot
  apply lower_le_six_fifths_rpow (by positivity)
  · fin_cases k <;> norm_num [pairMassEndpointLower]
  · fin_cases k <;> norm_num [pairMassEndpointLower, Matrix.cons_val]

theorem pairMassEndpoint_le_Upper (k : Fin 9) :
    pairMassEndpointRoot k ≤ pairMassEndpointUpper k := by
  unfold pairMassEndpointRoot
  apply six_fifths_rpow_le_upper (by positivity)
  · fin_cases k <;> norm_num [pairMassEndpointUpper]
  · fin_cases k <;> norm_num [pairMassEndpointUpper, Matrix.cons_val]

theorem pairMassEndpointLower_nonneg (k : Fin 9) : 0 ≤ pairMassEndpointLower k := by
  fin_cases k <;> norm_num [pairMassEndpointLower]

theorem pairMassEndpointUpper_nonneg (k : Fin 9) : 0 ≤ pairMassEndpointUpper k := by
  fin_cases k <;> norm_num [pairMassEndpointUpper]

end UnitDistance.Witness
