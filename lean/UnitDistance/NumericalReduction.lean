module

public import UnitDistance.LogBounds
public import UnitDistance.GaussianProfiles
public import UnitDistance.Certificate

@[expose] public section
set_option backward.privateInPublic true


/-! # Discharging the logarithm and compact-Gaussian numerical inputs

Only the actual pair functional and finite-place functional enclosures remain
inputs to `numericalBounds_of_pair_finite`. This does not discharge the field
tower, regulator identity, or every-large-field analytic ceiling.
-/

namespace UnitDistance

theorem log_pi_precise :
    (114472988584940017413 : ℝ) / 10^20 ≤ Real.log Real.pi ∧
      Real.log Real.pi ≤ (114472988584940017415 : ℝ) / 10^20 := by
  have h2 := log_two_precise
  simp only [div_one] at h2
  have hl := log_pi_lower_half.1
  have hu := log_pi_upper_half.2
  have hpl := Real.log_le_log (show (0 : ℝ) < 157079632679489661923 / 10^20 by norm_num)
    (show (157079632679489661923 : ℝ) / 10^20 ≤ Real.pi/2 by
      have h := Real.pi_gt_d20; norm_num at h ⊢; linarith)
  have hpu := Real.log_le_log (show 0 < Real.pi/2 by positivity)
    (show Real.pi/2 ≤ (314159265358979323847 : ℝ) / (2*10^20) by
      have h := Real.pi_lt_d20; norm_num at h ⊢; linarith)
  rw [Real.log_div Real.pi_ne_zero (by norm_num)] at hpl hpu
  norm_num at hl hu hpl hpu h2 ⊢
  constructor <;> linarith

theorem log_discriminant_upper : Real.log 15015 ≤ (9616804980418 : ℝ)/10^12 := by
  have h2 := log_two_precise.2
  simp only [div_one] at h2
  have hr := log_discriminant_reduced.2
  have heq : Real.log ((15015 : ℝ)/8192) = Real.log 15015 - 13*Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (8192 : ℝ) = 2^13 by norm_num,
      Real.log_pow]
    norm_num
  rw [heq] at hr
  linarith

namespace Witness

theorem log_increment_eq : Real.log increment =
    -4*Real.log 2 - Real.log ((125000 : ℝ)/83647) := by
  rw [show increment = (16*((125000 : ℝ)/83647))⁻¹ by norm_num [increment],
    Real.log_inv, Real.log_mul (by norm_num) (by norm_num),
    show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
  norm_num
  ring

theorem JCompact_log_eq : JCompact = -increment - increment*Real.log Real.pi +
    2*increment*Real.log 2 + increment*Real.log increment -
    (1+increment)*Real.log (1+increment) := by
  have hd := increment_pos
  have hp := witness_basic.2.2.1
  have h4 : Real.log (4*increment) = 2*Real.log 2 + Real.log increment := by
    rw [Real.log_mul (by norm_num) hd.ne', show (4 : ℝ) = 2^2 by norm_num,
      Real.log_pow]
    norm_num
  have h2 : Real.log (2*increment*p) =
      2*Real.log 2 + Real.log increment - Real.log (1+increment) := by
    rw [show 2*increment*p = 4*increment/(1+increment) by unfold p; ring,
      Real.log_div (by positivity) (by positivity), h4]
  rw [JCompact_eq, Real.log_div Real.pi_ne_zero (by positivity),
    Real.log_div Real.pi_ne_zero (by positivity), h4, h2]
  ring

theorem compactFunctional_bounds :
    -(207166792766 : ℝ)/10^12 ≤ JCompact ∧ JCompact ≤ -(207166792765 : ℝ)/10^12 := by
  have h2 := log_two_precise
  simp only [div_one] at h2
  have hπ := log_pi_precise
  have hr := log_increment_inverse_reduced
  have hd := log_one_add_increment
  rw [JCompact_log_eq, log_increment_eq]
  have heq : (1+increment) = (2083647 : ℝ)/2000000 := by norm_num [increment]
  rw [heq]
  norm_num [increment] at *
  constructor <;> linarith

theorem numericalBounds_of_pair_finite
    (hpair : (1379635324335 : ℝ)/10^12 ≤ JPair)
    (hfinite : (1033566922503 : ℝ)/10^12 ≤ finiteProfit) : NumericalBounds := by
  refine ⟨?_, log_discriminant_upper, ?_, compactFunctional_bounds, hpair, hfinite⟩
  · have h := log_two_precise
    simp only [div_one] at h
    constructor <;> linarith [h.1, h.2]
  · have h := log_pi_precise
    constructor <;> linarith [h.1, h.2]

theorem uniform_margin_of_pair_finite
    (hpair : (1379635324335 : ℝ)/10^12 ≤ JPair)
    (hfinite : (1033566922503 : ℝ)/10^12 ≤ finiteProfit)
    {θ : ℝ} (hθ : thetaMin ≤ θ) :
    (533 : ℝ)/10^8 < margin θ - 4*epsilon :=
  uniform_margin (numericalBounds_of_pair_finite hpair hfinite) hθ

end Witness
end UnitDistance
