module

public import UnitDistance.PairMassDegree12Data
public import UnitDistance.RationalPowerBounds

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
namespace UnitDistance.Witness

private theorem pairMassCenter_log_6_6 :
    (2277145830860774057 : ℝ) / 1000000000000000000 ≤ Real.log ((25555935937052487 : ℝ) / 2621440000000000) ∧
    Real.log ((25555935937052487 : ℝ) / 2621440000000000) ≤ (1138572915430387029 : ℝ) / 500000000000000000 := by
  have hb : (19770428918093812883 : ℝ) / 100000000000000000000 ≤ Real.log ((304650496686130607 : ℝ) / 250000000000000000) ∧
      Real.log ((304650496686130607 : ℝ) / 250000000000000000) ≤ (4942607229523453221 : ℝ) / 25000000000000000000 := by
    apply log_enclosure ((304650496686130607 : ℝ) / 250000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (25555935937052487 : ℝ) / 20971520000000000) (l := (304650496686130607 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((25555935937052487 : ℝ) / 2621440000000000) ((25555935937052487 : ℝ) / 20971520000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_6_6 :
    (4371461827959868687 : ℝ) / 1000000000000000000 ≤ Real.log ((3957963219369441 : ℝ) / 50000000000000) ∧
    Real.log ((3957963219369441 : ℝ) / 50000000000000) ≤ (273216364247491793 : ℝ) / 62500000000000000 := by
  have hb : (21257874460019683063 : ℝ) / 100000000000000000000 ≤ Real.log ((154607938256618789 : ℝ) / 125000000000000000) ∧
      Real.log ((154607938256618789 : ℝ) / 125000000000000000) ≤ (2657234307502460383 : ℝ) / 12500000000000000000 := by
    apply log_enclosure ((154607938256618789 : ℝ) / 125000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (3957963219369441 : ℝ) / 3200000000000000) (l := (154607938256618789 : ℝ) / 125000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((3957963219369441 : ℝ) / 50000000000000) ((3957963219369441 : ℝ) / 3200000000000000) (6) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_6_6 :
    pairMassCellCenter ⟨6, by decide⟩ ⟨6, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨6, by decide⟩ ⟨6, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (25555935937052487 : ℝ) / 2621440000000000)
    (by norm_num : 0 < (3957963219369441 : ℝ) / 50000000000000) (by norm_num [p, increment])
    pairMassCenter_log_6_6.2 pairMassPowerUpper_log_6_6.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_6_7 :
    (2402590431001377677 : ℝ) / 1000000000000000000 ≤ Real.log ((724288679118017 : ℝ) / 65536000000000) ∧
    Real.log ((724288679118017 : ℝ) / 65536000000000) ≤ (1201295215500688839 : ℝ) / 500000000000000000 := by
  have hb : (8078722233038543723 : ℝ) / 25000000000000000000 ≤ Real.log ((1381471021877321243 : ℝ) / 1000000000000000000) ∧
      Real.log ((1381471021877321243 : ℝ) / 1000000000000000000) ≤ (32314888932154174893 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1381471021877321243 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (724288679118017 : ℝ) / 524288000000000) (l := (1381471021877321243 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((724288679118017 : ℝ) / 65536000000000) ((724288679118017 : ℝ) / 524288000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_6_7 :
    (4612279202765876901 : ℝ) / 1000000000000000000 ≤ Real.log ((10071343458235213 : ℝ) / 100000000000000) ∧
    Real.log ((10071343458235213 : ℝ) / 100000000000000) ≤ (2306139601382938451 : ℝ) / 500000000000000000 := by
  have hb : (9067922388124100891 : ℝ) / 20000000000000000000 ≤ Real.log ((1573647415349252031 : ℝ) / 1000000000000000000) ∧
      Real.log ((1573647415349252031 : ℝ) / 1000000000000000000) ≤ (5667451492577563057 : ℝ) / 12500000000000000000 := by
    apply log_enclosure ((1573647415349252031 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (10071343458235213 : ℝ) / 6400000000000000) (l := (1573647415349252031 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((10071343458235213 : ℝ) / 100000000000000) ((10071343458235213 : ℝ) / 6400000000000000) (6) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_6_7 :
    pairMassCellCenter ⟨6, by decide⟩ ⟨7, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨6, by decide⟩ ⟨7, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (724288679118017 : ℝ) / 65536000000000)
    (by norm_num : 0 < (10071343458235213 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_6_7.2 pairMassPowerUpper_log_6_7.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

end UnitDistance.Witness
