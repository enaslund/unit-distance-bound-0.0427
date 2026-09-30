module

public import UnitDistance.PairFunctionalRelaxedCertificate
public import UnitDistance.FiniteFunctionalCertificate

@[expose] public section
set_option backward.privateInPublic true


/-! Additional certified numerical slack for a simpler overlap enclosure. -/

noncomputable section
namespace UnitDistance.Witness

def coarsePairOverlapLower : ℝ := 3484186885 / 10^7

theorem coarsePair_normalized_interval_score :
    (1379635321 : ℝ) / 10^9 <
      Real.log coarsePairOverlapLower
        + 2 * (1 + increment) * Real.log (s * p - 1)
        - 2 * increment * Real.log Real.pi
        + 2 * increment * Real.log a
        - (1 + increment) * Real.log relaxedPairMassUpper := by
  have hO := Real.log_le_sub_one_of_pos
    (show 0 < normalizedPairOverlapLower / coarsePairOverlapLower by
      norm_num [normalizedPairOverlapLower, coarsePairOverlapLower])
  have hM := Real.log_le_sub_one_of_pos
    (show 0 < relaxedPairMassUpper / normalizedPairMassUpper by
      norm_num [relaxedPairMassUpper, normalizedPairMassUpper])
  rw [Real.log_div (by norm_num [normalizedPairOverlapLower])
    (by norm_num [coarsePairOverlapLower])] at hO
  rw [Real.log_div (by norm_num [relaxedPairMassUpper])
    (by norm_num [normalizedPairMassUpper])] at hM
  have hs := normalized_interval_score
  norm_num [increment, normalizedPairOverlapLower, coarsePairOverlapLower,
    normalizedPairMassUpper, relaxedPairMassUpper] at hO hM hs ⊢
  linarith

theorem pairFunctional_of_coarse_overlap_and_betaMass
    (hoverlap : coarsePairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMassBetaIntegral ≤ relaxedPairMassUpper) :
    (1379635321 : ℝ) / 10^9 ≤ JPair := by
  have hOn : coarsePairOverlapLower ≤ normalizedPairOverlap :=
    (le_div_iff₀ pairArchScale_pos).mpr hoverlap
  have hMn : normalizedPairMass ≤ relaxedPairMassUpper := by
    rwa [normalizedPairMass_eq_betaIntegral]
  have hO := Real.log_le_log (by norm_num [coarsePairOverlapLower]) hOn
  have hM := Real.log_le_log normalizedPairMass_pos hMn
  have hs := coarsePair_normalized_interval_score
  rw [JPair_eq_normalized]
  norm_num [increment] at hs ⊢
  linarith

/-- The weaker pair bound preserves the original positive growth rate. -/
theorem uniform_margin_of_coarsePair
    (hpair : (1379635321 : ℝ) / 10^9 ≤ JPair)
    {θ : ℝ} (hθ : thetaMin ≤ θ) :
    (533 : ℝ) / 10^8 < margin θ - 4*epsilon := by
  have hπ := UnitDistance.log_pi_precise
  have hC := compactFunctional_bounds
  have h2 := log_two_precise
  simp only [div_one] at h2
  have h15 := UnitDistance.log_discriminant_upper
  have hF := finiteProfit_lower
  have hslope : 0 < -Real.log Real.pi - 2*JCompact + JPair := by
    linarith [hπ.2, hC.2]
  have hmono : margin thetaMin ≤ margin θ := by
    have hp := mul_nonneg (sub_nonneg.mpr hθ) hslope.le
    unfold margin
    nlinarith
  have hmin : (533 : ℝ) / 10^8 < margin thetaMin - 4*epsilon := by
    norm_num [margin, thetaMin, epsilon, logRD, ceiling, increment] at *
    linarith [h2.1, h2.2, hπ.1, hC.1]
  linarith

end UnitDistance.Witness
