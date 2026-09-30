module

public import UnitDistance.PairFunctionalSharperCertificateAstra

@[expose] public section
set_option backward.privateInPublic true


/-! Refined pair-functional threshold from the exact coefficient
`1 + increment` in the mass logarithm. -/

noncomputable section
set_option autoImplicit false
namespace UnitDistance.Witness

private theorem log_difference_le_ratio_threshold {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Real.log x - Real.log y ≤ (x - y) / y := by
  rw [← Real.log_div hx.ne' hy.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  convert h using 1 <;> field_simp <;> ring

/-- With the sharper mass endpoint, the coarse normalized score exceeds
`1.379633`. -/
theorem sharperPair_normalized_interval_score_1379633_astra :
    (1379633 : ℝ) / 1000000 <
      Real.log coarsePairOverlapLower
        + 2 * (1 + increment) * Real.log (s * p - 1)
        - 2 * increment * Real.log Real.pi
        + 2 * increment * Real.log a
        - (1 + increment) * Real.log ((38968863 : ℝ) / 1000000) := by
  have hM := log_difference_le_ratio_threshold
    (x := (38968863 : ℝ) / 1000000) (y := relaxedPairMassUpper)
    (by norm_num) (by norm_num [relaxedPairMassUpper])
  have hs := coarsePair_normalized_interval_score
  norm_num [increment, relaxedPairMassUpper] at hM hs ⊢
  linarith

/-- Coarse overlap and the sharper mass bound imply `JPair ≥ 1.379633`. -/
theorem pairFunctional_of_coarse_overlap_and_sharper_betaMass_1379633_astra
    (hoverlap : coarsePairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMassBetaIntegral ≤ (38968863 : ℝ) / 1000000) :
    (1379633 : ℝ) / 1000000 ≤ JPair := by
  have hOn : coarsePairOverlapLower ≤ normalizedPairOverlap :=
    (le_div_iff₀ pairArchScale_pos).mpr hoverlap
  have hMn : normalizedPairMass ≤ (38968863 : ℝ) / 1000000 := by
    rwa [normalizedPairMass_eq_betaIntegral]
  have hO := Real.log_le_log (by norm_num [coarsePairOverlapLower]) hOn
  have hM := Real.log_le_log normalizedPairMass_pos hMn
  have hs := sharperPair_normalized_interval_score_1379633_astra
  rw [JPair_eq_normalized]
  norm_num [increment] at hs ⊢
  linarith

/-- Fully internal strengthened pair-functional lower bound. -/
theorem JPair_ge_1379633_astra :
    (1379633 : ℝ) / 1000000 ≤ JPair :=
  pairFunctional_of_coarse_overlap_and_sharper_betaMass_1379633_astra
    pairOverlap_coarse_lower pairMassBetaIntegral_le_38968863

/-- The strengthened pair endpoint leaves more than `4e-6` uniform margin. -/
theorem uniform_margin_of_sharperPair_astra
    (hpair : (1379633 : ℝ) / 1000000 ≤ JPair)
    {θ : ℝ} (hθ : thetaMin ≤ θ) :
    (400 : ℝ) / 10^8 < margin θ - 4 * epsilon := by
  have hπ := UnitDistance.log_pi_precise
  have hC := compactFunctional_bounds
  have h2 := log_two_precise
  simp only [div_one] at h2
  have h15 := UnitDistance.log_discriminant_upper
  have hF := finiteProfit_lower
  have hslope : 0 < -Real.log Real.pi - 2 * JCompact + JPair := by
    linarith [hπ.2, hC.2]
  have hmono : margin thetaMin ≤ margin θ := by
    have hp := mul_nonneg (sub_nonneg.mpr hθ) hslope.le
    unfold margin
    nlinarith
  have hmin : (400 : ℝ) / 10^8 < margin thetaMin - 4 * epsilon := by
    norm_num [margin, thetaMin, epsilon, logRD, ceiling, increment] at *
    linarith [h2.1, h2.2, hπ.1, hC.1]
  linarith

/-- Fully internal `4e-6` margin consequence. -/
theorem uniform_margin_sharper_astra {θ : ℝ} (hθ : thetaMin ≤ θ) :
    (400 : ℝ) / 10^8 < margin θ - 4 * epsilon :=
  uniform_margin_of_sharperPair_astra JPair_ge_1379633_astra hθ

end UnitDistance.Witness
