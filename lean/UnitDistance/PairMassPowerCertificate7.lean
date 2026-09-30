module

public import UnitDistance.PairMassDegree12Data
public import UnitDistance.RationalPowerBounds

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
namespace UnitDistance.Witness

private theorem pairMassCenter_log_7_7 :
    (629393252983314277 : ℝ) / 250000000000000000 ≤ Real.log ((32501843052713607 : ℝ) / 2621440000000000) ∧
    Real.log ((32501843052713607 : ℝ) / 2621440000000000) ≤ (251757301193325711 : ℝ) / 100000000000000000 := by
  have hb : (10953286756335529507 : ℝ) / 25000000000000000000 ≤ Real.log ((1549808647761993741 : ℝ) / 1000000000000000000) ∧
      Real.log ((1549808647761993741 : ℝ) / 1000000000000000000) ≤ (43813147025342118029 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1549808647761993741 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (32501843052713607 : ℝ) / 20971520000000000) (l := (1549808647761993741 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((32501843052713607 : ℝ) / 2621440000000000) ((32501843052713607 : ℝ) / 20971520000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_7_7 :
    (4833012524546158059 : ℝ) / 1000000000000000000 ≤ Real.log ((12558873048192631 : ℝ) / 100000000000000) ∧
    Real.log ((12558873048192631 : ℝ) / 100000000000000) ≤ (4833012524546158061 : ℝ) / 1000000000000000000 := by
  have hb : (33706472059324310173 : ℝ) / 50000000000000000000 ≤ Real.log ((1962323913780098593 : ℝ) / 1000000000000000000) ∧
      Real.log ((1962323913780098593 : ℝ) / 1000000000000000000) ≤ (67412944118648620347 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1962323913780098593 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (12558873048192631 : ℝ) / 6400000000000000) (l := (1962323913780098593 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((12558873048192631 : ℝ) / 100000000000000) ((12558873048192631 : ℝ) / 6400000000000000) (6) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_7_7 :
    pairMassCellCenter ⟨7, by decide⟩ ⟨7, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨7, by decide⟩ ⟨7, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (32501843052713607 : ℝ) / 2621440000000000)
    (by norm_num : 0 < (12558873048192631 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_7_7.2 pairMassPowerUpper_log_7_7.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

end UnitDistance.Witness
