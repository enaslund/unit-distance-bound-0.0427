module

public import UnitDistance.PairFunctionalCoarseCertificate
public import UnitDistance.FiniteFunctionalCertificate

@[expose] public section
set_option backward.privateInPublic true


/-! Additional certified numerical slack for a simpler overlap enclosure. -/

noncomputable section
namespace UnitDistance.Witness

def widePairMassUpper : ℝ := 389689 / 10000

theorem widePair_normalized_interval_score :
    (137963 : ℝ) / 10^5 <
      Real.log coarsePairOverlapLower
        + 2 * (1 + increment) * Real.log (s * p - 1)
        - 2 * increment * Real.log Real.pi
        + 2 * increment * Real.log a
        - (1 + increment) * Real.log widePairMassUpper := by
  have hO := Real.log_le_sub_one_of_pos
    (show 0 < normalizedPairOverlapLower / coarsePairOverlapLower by
      norm_num [normalizedPairOverlapLower, coarsePairOverlapLower])
  have hM := Real.log_le_sub_one_of_pos
    (show 0 < widePairMassUpper / normalizedPairMassUpper by
      norm_num [widePairMassUpper, normalizedPairMassUpper])
  rw [Real.log_div (by norm_num [normalizedPairOverlapLower])
    (by norm_num [coarsePairOverlapLower])] at hO
  rw [Real.log_div (by norm_num [widePairMassUpper])
    (by norm_num [normalizedPairMassUpper])] at hM
  have hs := normalized_interval_score
  norm_num [increment, normalizedPairOverlapLower, coarsePairOverlapLower,
    normalizedPairMassUpper, widePairMassUpper] at hO hM hs ⊢
  linarith

theorem pairFunctional_of_wide_overlap_and_betaMass
    (hoverlap : coarsePairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMassBetaIntegral ≤ widePairMassUpper) :
    (137963 : ℝ) / 10^5 ≤ JPair := by
  have hOn : coarsePairOverlapLower ≤ normalizedPairOverlap :=
    (le_div_iff₀ pairArchScale_pos).mpr hoverlap
  have hMn : normalizedPairMass ≤ widePairMassUpper := by
    rwa [normalizedPairMass_eq_betaIntegral]
  have hO := Real.log_le_log (by norm_num [coarsePairOverlapLower]) hOn
  have hM := Real.log_le_log normalizedPairMass_pos hMn
  have hs := widePair_normalized_interval_score
  rw [JPair_eq_normalized]
  norm_num [increment] at hs ⊢
  linarith

/-- A weaker pair bound still gives a positive growth rate. -/
theorem uniform_margin_of_widePair
    (hpair : (137963 : ℝ) / 10^5 ≤ JPair)
    {θ : ℝ} (hθ : thetaMin ≤ θ) :
    (100 : ℝ) / 10^8 < margin θ - 4*epsilon := by
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
  have hmin : (100 : ℝ) / 10^8 < margin thetaMin - 4*epsilon := by
    norm_num [margin, thetaMin, epsilon, logRD, ceiling, increment] at *
    linarith [h2.1, h2.2, hπ.1, hC.1]
  linarith

end UnitDistance.Witness
