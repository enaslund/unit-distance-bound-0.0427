module

public import UnitDistance.PairMassNormalization

@[expose] public section
set_option backward.privateInPublic true


/-! Slightly wider directed endpoints still imply the original pair threshold. -/

noncomputable section
namespace UnitDistance.Witness

def relaxedPairOverlapLower : ℝ := 3484186894703 / 10^10
def relaxedPairMassUpper : ℝ := 3896878165633 / 10^11

private theorem log_difference_le_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log x - Real.log y ≤ (x - y) / y := by
  rw [← Real.log_div hx.ne' hy.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  convert h using 1 <;> field_simp <;> ring

theorem relaxed_normalized_interval_score :
    (1379635324335 : ℝ) / 10^12 <
      Real.log relaxedPairOverlapLower
        + 2 * (1 + increment) * Real.log (s * p - 1)
        - 2 * increment * Real.log Real.pi
        + 2 * increment * Real.log a
        - (1 + increment) * Real.log relaxedPairMassUpper := by
  have hO := log_difference_le_ratio (x := normalizedPairOverlapLower)
    (y := relaxedPairOverlapLower)
    (by norm_num [normalizedPairOverlapLower]) (by norm_num [relaxedPairOverlapLower])
  have hM := log_difference_le_ratio (x := relaxedPairMassUpper)
    (y := normalizedPairMassUpper)
    (by norm_num [relaxedPairMassUpper]) (by norm_num [normalizedPairMassUpper])
  have hscore := normalized_interval_score
  norm_num [normalizedPairOverlapLower, relaxedPairOverlapLower,
    relaxedPairMassUpper, normalizedPairMassUpper] at hO hM
  norm_num [increment, normalizedPairOverlapLower, normalizedPairMassUpper,
    relaxedPairOverlapLower, relaxedPairMassUpper] at hscore ⊢
  linarith

theorem pairFunctional_of_relaxed_intervals
    (hoverlap : relaxedPairOverlapLower ≤ normalizedPairOverlap)
    (hmass : normalizedPairMass ≤ relaxedPairMassUpper) :
    (1379635324335 : ℝ) / 10^12 ≤ JPair := by
  have hO := Real.log_le_log (by norm_num [relaxedPairOverlapLower]) hoverlap
  have hM := Real.log_le_log normalizedPairMass_pos hmass
  have hscore := relaxed_normalized_interval_score
  rw [JPair_eq_normalized]
  norm_num [increment] at hscore ⊢
  linarith

theorem pairFunctional_of_relaxed_overlap_and_betaMass
    (hoverlap : relaxedPairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMassBetaIntegral ≤ relaxedPairMassUpper) :
    (1379635324335 : ℝ) / 10^12 ≤ JPair := by
  apply pairFunctional_of_relaxed_intervals
  · exact (le_div_iff₀ pairArchScale_pos).mpr hoverlap
  · rwa [normalizedPairMass_eq_betaIntegral]

end UnitDistance.Witness
