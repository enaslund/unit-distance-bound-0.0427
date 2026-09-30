module

public import UnitDistance.PairMassDegree12Data
public import UnitDistance.RationalPowerBounds

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
namespace UnitDistance.Witness

private theorem pairMassCenter_log_5_5 :
    (2031919049819669963 : ℝ) / 1000000000000000000 ≤ Real.log ((3999642261495923 : ℝ) / 524288000000000) ∧
    Real.log ((3999642261495923 : ℝ) / 524288000000000) ≤ (507979762454917491 : ℝ) / 250000000000000000 := by
  have hb : (32281234434988967213 : ℝ) / 50000000000000000000 ≤ Real.log ((953589024900418043 : ℝ) / 500000000000000000) ∧
      Real.log ((953589024900418043 : ℝ) / 500000000000000000) ≤ (64562468869977934427 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((953589024900418043 : ℝ) / 500000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (3999642261495923 : ℝ) / 2097152000000000) (l := (953589024900418043 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((3999642261495923 : ℝ) / 524288000000000) ((3999642261495923 : ℝ) / 2097152000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_5_5 :
    (3900697286670285581 : ℝ) / 1000000000000000000 ≤ Real.log ((1235922719687829 : ℝ) / 25000000000000) ∧
    Real.log ((1235922719687829 : ℝ) / 25000000000000) ≤ (3900697286670285583 : ℝ) / 1000000000000000000 := by
  have hb : (43496138387055903431 : ℝ) / 100000000000000000000 ≤ Real.log ((1235922719687829 : ℝ) / 800000000000000) ∧
      Real.log ((1235922719687829 : ℝ) / 800000000000000) ≤ (5437017298381987929 : ℝ) / 12500000000000000000 := by
    apply log_enclosure ((1235922719687829 : ℝ) / 800000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (1235922719687829 : ℝ) / 800000000000000) (l := (1235922719687829 : ℝ) / 800000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1235922719687829 : ℝ) / 25000000000000) ((1235922719687829 : ℝ) / 800000000000000) (5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_5_5 :
    pairMassCellCenter ⟨5, by decide⟩ ⟨5, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨5, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (3999642261495923 : ℝ) / 524288000000000)
    (by norm_num : 0 < (1235922719687829 : ℝ) / 25000000000000) (by norm_num [p, increment])
    pairMassCenter_log_5_5.2 pairMassPowerUpper_log_5_5.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_5_6 :
    (2159495742913896309 : ℝ) / 1000000000000000000 ≤ Real.log ((141996298700341 : ℝ) / 16384000000000) ∧
    Real.log ((141996298700341 : ℝ) / 16384000000000) ≤ (2159495742913896311 : ℝ) / 1000000000000000000 := by
  have hb : (800542012340603817 : ℝ) / 10000000000000000000 ≤ Real.log ((1083345784762123107 : ℝ) / 1000000000000000000) ∧
      Real.log ((1083345784762123107 : ℝ) / 1000000000000000000) ≤ (8005420123406038171 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1083345784762123107 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (141996298700341 : ℝ) / 131072000000000) (l := (1083345784762123107 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((141996298700341 : ℝ) / 16384000000000) ((141996298700341 : ℝ) / 131072000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_5_6 :
    (1036401915926208453 : ℝ) / 250000000000000000 ≤ Real.log ((6315598784532529 : ℝ) / 100000000000000) ∧
    Real.log ((6315598784532529 : ℝ) / 100000000000000) ≤ (2072803831852416907 : ℝ) / 500000000000000000 := by
  have hb : (1062299626414230103 : ℝ) / 1562500000000000000 ≤ Real.log ((123351538760400957 : ℝ) / 62500000000000000) ∧
      Real.log ((123351538760400957 : ℝ) / 62500000000000000) ≤ (67987176090510726593 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((123351538760400957 : ℝ) / 62500000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (6315598784532529 : ℝ) / 3200000000000000) (l := (123351538760400957 : ℝ) / 62500000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((6315598784532529 : ℝ) / 100000000000000) ((6315598784532529 : ℝ) / 3200000000000000) (5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_5_6 :
    pairMassCellCenter ⟨5, by decide⟩ ⟨6, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨5, by decide⟩ ⟨6, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (141996298700341 : ℝ) / 16384000000000)
    (by norm_num : 0 < (6315598784532529 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_5_6.2 pairMassPowerUpper_log_5_6.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_5_7 :
    (2295041392411153041 : ℝ) / 1000000000000000000 ≤ Real.log ((26017390440279637 : ℝ) / 2621440000000000) ∧
    Real.log ((26017390440279637 : ℝ) / 2621440000000000) ≤ (2295041392411153043 : ℝ) / 1000000000000000000 := by
  have hb : (4311997014626342263 : ℝ) / 20000000000000000000 ≤ Real.log ((620302926070204663 : ℝ) / 500000000000000000) ∧
      Real.log ((620302926070204663 : ℝ) / 500000000000000000) ≤ (5389996268282927829 : ℝ) / 25000000000000000000 := by
    apply log_enclosure ((620302926070204663 : ℝ) / 500000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (26017390440279637 : ℝ) / 20971520000000000) (l := (620302926070204663 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((26017390440279637 : ℝ) / 2621440000000000) ((26017390440279637 : ℝ) / 20971520000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_5_7 :
    (4405816133752316311 : ℝ) / 1000000000000000000 ≤ Real.log ((8192597812213133 : ℝ) / 100000000000000) ∧
    Real.log ((8192597812213133 : ℝ) / 100000000000000) ≤ (4405816133752316313 : ℝ) / 1000000000000000000 := by
  have hb : (12346652519632222737 : ℝ) / 50000000000000000000 ≤ Real.log ((1280093408158302031 : ℝ) / 1000000000000000000) ∧
      Real.log ((1280093408158302031 : ℝ) / 1000000000000000000) ≤ (987732201570577819 : ℝ) / 4000000000000000000 := by
    apply log_enclosure ((1280093408158302031 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (8192597812213133 : ℝ) / 6400000000000000) (l := (1280093408158302031 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((8192597812213133 : ℝ) / 100000000000000) ((8192597812213133 : ℝ) / 6400000000000000) (6) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_5_7 :
    pairMassCellCenter ⟨5, by decide⟩ ⟨7, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨5, by decide⟩ ⟨7, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (26017390440279637 : ℝ) / 2621440000000000)
    (by norm_num : 0 < (8192597812213133 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_5_7.2 pairMassPowerUpper_log_5_7.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

end UnitDistance.Witness
