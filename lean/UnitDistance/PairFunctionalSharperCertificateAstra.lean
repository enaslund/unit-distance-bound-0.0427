module

public import UnitDistance.PairMassSharperCertificateAstra
public import UnitDistance.PairOverlapCoarseLower

@[expose] public section
set_option backward.privateInPublic true


/-! Pair-functional consequence of the sharper degree-three mass sum. -/

noncomputable section
set_option autoImplicit false
namespace UnitDistance.Witness

private theorem log_difference_le_ratio_astra {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Real.log x - Real.log y ≤ (x - y) / y := by
  rw [← Real.log_div hx.ne' hy.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  convert h using 1 <;> field_simp <;> ring

/-- A conservative intermediate score from the six-decimal mass endpoint.
`PairFunctionalSharperThresholdAstra` records the stronger `1.379633`
consequence using the same directed logarithm estimate. -/
theorem sharperPair_normalized_interval_score_astra :
    (1379631 : ℝ) / 1000000 <
      Real.log coarsePairOverlapLower
        + 2 * (1 + increment) * Real.log (s * p - 1)
        - 2 * increment * Real.log Real.pi
        + 2 * increment * Real.log a
        - (1 + increment) * Real.log ((38968863 : ℝ) / 1000000) := by
  have hM := log_difference_le_ratio_astra
    (x := (38968863 : ℝ) / 1000000) (y := relaxedPairMassUpper)
    (by norm_num) (by norm_num [relaxedPairMassUpper])
  have hs := coarsePair_normalized_interval_score
  norm_num [increment, relaxedPairMassUpper] at hM hs ⊢
  linarith

/-- Coarse overlap plus the sharper mass certificate imply `JPair ≥ 1.379631`. -/
theorem pairFunctional_of_coarse_overlap_and_sharper_betaMass_astra
    (hoverlap : coarsePairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMassBetaIntegral ≤ (38968863 : ℝ) / 1000000) :
    (1379631 : ℝ) / 1000000 ≤ JPair := by
  have hOn : coarsePairOverlapLower ≤ normalizedPairOverlap :=
    (le_div_iff₀ pairArchScale_pos).mpr hoverlap
  have hMn : normalizedPairMass ≤ (38968863 : ℝ) / 1000000 := by
    rwa [normalizedPairMass_eq_betaIntegral]
  have hO := Real.log_le_log (by norm_num [coarsePairOverlapLower]) hOn
  have hM := Real.log_le_log normalizedPairMass_pos hMn
  have hs := sharperPair_normalized_interval_score_astra
  rw [JPair_eq_normalized]
  norm_num [increment] at hs ⊢
  linarith

/-- Fully internal pair-functional lower bound from the checked overlap and
mass certificates. -/
theorem JPair_ge_1379631_astra :
    (1379631 : ℝ) / 1000000 ≤ JPair :=
  pairFunctional_of_coarse_overlap_and_sharper_betaMass_astra
    pairOverlap_coarse_lower pairMassBetaIntegral_le_38968863

end UnitDistance.Witness
