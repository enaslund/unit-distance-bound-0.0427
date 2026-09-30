module

public import UnitDistance.StudentOverlap
public import UnitDistance.NumericalReduction
public import UnitDistance.RationalPowerBounds

@[expose] public section
set_option backward.privateInPublic true


/-!
# A two-interval certificate interface for the pair functional

The external profile calculation naturally bounds two dimensionless
quantities: the mass after removing its exact radial scale, and the overlap
after removing the same scale.  This file connects those quantities to the
literal integrals in `Witness.lean` and checks all logarithmic arithmetic
needed by the published pair-functional threshold.

Thus the single hypothesis on `JPair` can be replaced by two direct interval
facts about independently defined integrals.  The analytic evaluation of
those two intervals remains a separate obligation.
-/

noncomputable section

namespace UnitDistance.Witness

/-- The common `pi^2 / a^2` scale in the complex-pair mass and overlap. -/
def pairArchScale : ℝ := Real.pi ^ 2 / a ^ 2

/-- The literal mass with its exact radial scale removed.  In the manuscript
this is the beta expectation denoted by `mathcal A`. -/
def normalizedPairMass : ℝ := pairMass / (pairArchScale / (s * p - 1) ^ 2)

/-- The literal overlap with its exact radial scale removed. -/
def normalizedPairOverlap : ℝ := pairOverlap / pairArchScale

/-- Lower endpoint printed by the directed overlap calculation. -/
def normalizedPairOverlapLower : ℝ :=
  (3484186894704059951 : ℝ) / 10000000000000000

/-- Upper endpoint printed by the directed mass calculation. -/
def normalizedPairMassUpper : ℝ :=
  (389687816563247561 : ℝ) / 10000000000000000

theorem pairExponentGap : s * p - 1 = (6 : ℝ) / 5 := by
  norm_num [s, p, increment]

theorem pairArchScale_pos : 0 < pairArchScale := by
  unfold pairArchScale
  exact div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos witness_basic.2.1)

theorem pairMassScale_pos : 0 < pairArchScale / (s * p - 1) ^ 2 := by
  have hgap : 0 < s * p - 1 := by rw [pairExponentGap]; norm_num
  exact div_pos pairArchScale_pos (sq_pos_of_pos hgap)

theorem normalizedPairMass_pos : 0 < normalizedPairMass := by
  unfold normalizedPairMass
  have hgap : 0 < s * p - 1 := by rw [pairExponentGap]; norm_num
  exact div_pos pairMass_pos (div_pos pairArchScale_pos (sq_pos_of_pos hgap))

theorem normalizedPairOverlap_pos : 0 < normalizedPairOverlap := by
  exact div_pos pairOverlap_pos pairArchScale_pos

theorem JPair_eq_normalized :
    JPair = Real.log normalizedPairOverlap
      + 2 * (1 + increment) * Real.log (s * p - 1)
      - 2 * increment * Real.log Real.pi
      + 2 * increment * Real.log a
      - (1 + increment) * Real.log normalizedPairMass := by
  have ha : a ≠ 0 := ne_of_gt witness_basic.2.1
  have hgap : s * p - 1 ≠ 0 := by rw [pairExponentGap]; norm_num
  have hscale : pairArchScale ≠ 0 := ne_of_gt pairArchScale_pos
  have hmassScale : pairArchScale / (s * p - 1) ^ 2 ≠ 0 :=
    div_ne_zero hscale (pow_ne_zero 2 hgap)
  have hO : pairOverlap = normalizedPairOverlap * pairArchScale := by
    rw [normalizedPairOverlap, div_mul_cancel₀ _ hscale]
  have hM : pairMass = normalizedPairMass *
      (pairArchScale / (s * p - 1) ^ 2) := by
    rw [normalizedPairMass, div_mul_cancel₀ _ hmassScale]
  have hscaleLog : Real.log pairArchScale =
      2 * Real.log Real.pi - 2 * Real.log a := by
    rw [pairArchScale, Real.log_div (pow_ne_zero 2 Real.pi_ne_zero) (pow_ne_zero 2 ha),
      Real.log_pow, Real.log_pow]
    ring
  have hmassScaleLog : Real.log (pairArchScale / (s * p - 1) ^ 2) =
      2 * Real.log Real.pi - 2 * Real.log a - 2 * Real.log (s * p - 1) := by
    rw [Real.log_div hscale (pow_ne_zero 2 hgap), Real.log_pow, hscaleLog]
    ring
  rw [JPair, hO, hM,
    Real.log_mul (ne_of_gt normalizedPairOverlap_pos) hscale,
    Real.log_mul (ne_of_gt normalizedPairMass_pos) hmassScale,
    hscaleLog, hmassScaleLog]
  ring

private theorem log_gap_lower :
    (18232155679395462621 : ℝ) / 10 ^ 20 ≤ Real.log ((6 : ℝ) / 5) := by
  exact (log_enclosure ((6 : ℝ) / 5) 25 (by norm_num)
    ((18232155679395462621 : ℝ) / 10 ^ 20)
    ((18232155679395462622 : ℝ) / 10 ^ 20)
    (by norm_num [Finset.sum_range_succ])
    (by norm_num [Finset.sum_range_succ])).1

private theorem log_a_reduced :
    (52237168652613924669 : ℝ) / 10 ^ 20 ≤
        Real.log ((257266483516 : ℝ) / 152587890625) ∧
      Real.log ((257266483516 : ℝ) / 152587890625) ≤
        (52237168652613924670 : ℝ) / 10 ^ 20 := by
  apply log_enclosure ((257266483516 : ℝ) / 152587890625) 25 (by norm_num)
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

private theorem log_a_lower :
    (-11261130382992931014 : ℝ) / 10 ^ 18 ≤ Real.log a := by
  have h2 := log_two_precise
  simp only [div_one] at h2
  have hs := log_scale_two a ((257266483516 : ℝ) / 152587890625) (-17)
    (by norm_num) (by norm_num [a])
  rw [hs]
  norm_num
  linarith [log_a_reduced.1, h2.2]

private theorem log_overlap_reduced :
    (30822744277529962649 : ℝ) / 10 ^ 20 ≤
        Real.log ((3484186894704059951 : ℝ) / 2560000000000000000) ∧
      Real.log ((3484186894704059951 : ℝ) / 2560000000000000000) ≤
        (30822744277529962650 : ℝ) / 10 ^ 20 := by
  apply log_enclosure
      ((3484186894704059951 : ℝ) / 2560000000000000000) 25 (by norm_num)
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

private theorem log_normalizedPairOverlapLower :
    (5853404887254862101 : ℝ) / 10 ^ 18 ≤
      Real.log normalizedPairOverlapLower := by
  have h2 := log_two_precise
  simp only [div_one] at h2
  have hs := log_scale_two normalizedPairOverlapLower
    ((3484186894704059951 : ℝ) / 2560000000000000000) 8
    (by norm_num) (by norm_num [normalizedPairOverlapLower])
  rw [hs]
  norm_num
  linarith [log_overlap_reduced.1, h2.1]

private theorem log_mass_reduced :
    (19702495243181089328 : ℝ) / 10 ^ 20 ≤
        Real.log ((389687816563247561 : ℝ) / 320000000000000000) ∧
      Real.log ((389687816563247561 : ℝ) / 320000000000000000) ≤
        (19702495243181089329 : ℝ) / 10 ^ 20 := by
  apply log_enclosure
      ((389687816563247561 : ℝ) / 320000000000000000) 25 (by norm_num)
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

private theorem log_normalizedPairMassUpper :
    Real.log normalizedPairMassUpper ≤
      (3662760855231537441 : ℝ) / 10 ^ 18 := by
  have h2 := log_two_precise
  simp only [div_one] at h2
  have hs := log_scale_two normalizedPairMassUpper
    ((389687816563247561 : ℝ) / 320000000000000000) 5
    (by norm_num) (by norm_num [normalizedPairMassUpper])
  rw [hs]
  norm_num
  linarith [log_mass_reduced.2, h2.2]

/-- Kernel-checked logarithmic arithmetic leaves a strict margin of more than
`7.4e-13` above the pair-functional threshold. -/
theorem normalized_interval_score :
    (1379635324335 : ℝ) / 10 ^ 12 + (74 : ℝ) / 10 ^ 14 <
      Real.log normalizedPairOverlapLower
        + 2 * (1 + increment) * Real.log (s * p - 1)
        - 2 * increment * Real.log Real.pi
        + 2 * increment * Real.log a
        - (1 + increment) * Real.log normalizedPairMassUpper := by
  have hpi := UnitDistance.log_pi_precise.2
  have hgap := log_gap_lower
  rw [pairExponentGap]
  norm_num [increment] at hpi hgap ⊢
  linarith [log_normalizedPairOverlapLower, log_normalizedPairMassUpper, log_a_lower]

/-- The two outward interval facts produced by the profile computation imply
the exact `hpair` premise used by the full theorem. -/
theorem pairFunctional_of_normalized_intervals
    (hoverlap : normalizedPairOverlapLower ≤ normalizedPairOverlap)
    (hmass : normalizedPairMass ≤ normalizedPairMassUpper) :
    (1379635324335 : ℝ) / 10 ^ 12 ≤ JPair := by
  have hOlog : Real.log normalizedPairOverlapLower ≤
      Real.log normalizedPairOverlap :=
    Real.log_le_log (by norm_num [normalizedPairOverlapLower]) hoverlap
  have hMlog : Real.log normalizedPairMass ≤
      Real.log normalizedPairMassUpper :=
    Real.log_le_log normalizedPairMass_pos hmass
  rw [JPair_eq_normalized]
  have hscore := normalized_interval_score
  norm_num [increment] at hscore ⊢
  linarith

theorem normalizedPairOverlap_interval_iff :
    normalizedPairOverlapLower ≤ normalizedPairOverlap ↔
      normalizedPairOverlapLower * pairArchScale ≤ pairOverlap := by
  unfold normalizedPairOverlap
  exact le_div_iff₀ pairArchScale_pos

theorem normalizedPairMass_interval_iff :
    normalizedPairMass ≤ normalizedPairMassUpper ↔
      pairMass ≤ normalizedPairMassUpper *
        (pairArchScale / (s * p - 1) ^ 2) := by
  unfold normalizedPairMass
  exact div_le_iff₀ pairMassScale_pos

/-- Equivalent certificate interface stated directly as bounds on the two
literal integrals from `Witness.lean`. -/
theorem pairFunctional_of_integral_intervals
    (hoverlap : normalizedPairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMass ≤ normalizedPairMassUpper *
      (pairArchScale / (s * p - 1) ^ 2)) :
    (1379635324335 : ℝ) / 10 ^ 12 ≤ JPair :=
  pairFunctional_of_normalized_intervals
    (normalizedPairOverlap_interval_iff.mpr hoverlap)
    (normalizedPairMass_interval_iff.mpr hmass)

end UnitDistance.Witness
