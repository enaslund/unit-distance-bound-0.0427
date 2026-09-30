module

public import UnitDistance.GaussianProfiles

@[expose] public section
set_option backward.privateInPublic true


/-!
# Gaussian kernel for the pair-overlap certificate

This file evaluates the unequal-coefficient shifted complex Gaussian which
occurs after applying the Laplace representation to two Student weights.  It
is kept separate from the witness-specific finite certificate: all parameters
below are arbitrary positive real numbers.
-/

noncomputable section

open MeasureTheory

namespace UnitDistance

private theorem pairOverlap_real_complete_square (r t x y : ℝ)
    (hrt : r + t ≠ 0) :
    r * x ^ 2 + t * (x + y) ^ 2 =
      (r + t) * (x + t / (r + t) * y) ^ 2 +
        (r * t / (r + t)) * y ^ 2 := by
  field_simp [hrt]
  ring

/-- Completing the square with two positive (or merely nonzero-sum)
coefficients.  The statement uses the complex norm because that is the
literal space of one coordinate of the pair witness. -/
theorem pairOverlap_gaussian_complete_square (r t : ℝ) (h z : ℂ)
    (hrt : r + t ≠ 0) :
    r * ‖z‖ ^ 2 + t * ‖z + h‖ ^ 2 =
      (r + t) * ‖z + (t / (r + t) : ℝ) • h‖ ^ 2 +
        (r * t / (r + t)) * ‖h‖ ^ 2 := by
  have hre := pairOverlap_real_complete_square r t z.re h.re hrt
  have him := pairOverlap_real_complete_square r t z.im h.im hrt
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im]
  linear_combination hre + him

/-- The exact complex Gaussian convolution with arbitrary positive
coefficients and displacement. -/
theorem pairOverlap_gaussian_integral {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (h : ℂ) :
    (∫ z : ℂ, Real.exp (-(r * ‖z‖ ^ 2 + t * ‖z + h‖ ^ 2))) =
      Real.exp (-(r * t / (r + t)) * ‖h‖ ^ 2) * (Real.pi / (r + t)) := by
  have hrt : 0 < r + t := add_pos hr ht
  have hs (z : ℂ) := pairOverlap_gaussian_complete_square r t h z hrt.ne'
  simp_rw [hs, neg_add, Real.exp_add]
  rw [integral_mul_const]
  rw [mul_comm]
  have hg (z : ℂ) : Real.exp (-((r + t) * ‖z + (t / (r + t) : ℝ) • h‖ ^ 2)) =
      complexGaussian (r + t) (z + (t / (r + t) : ℝ) • h) := by
    unfold complexGaussian
    congr 1
    ring
  simp_rw [hg]
  rw [integral_add_right_eq_self, complexGaussian_integral hrt]
  ring

/-- Integrability needed for Tonelli/Fubini in the subsequent Laplace
reduction. -/
theorem pairOverlap_gaussian_integrable {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (h : ℂ) :
    Integrable (fun z : ℂ =>
      Real.exp (-(r * ‖z‖ ^ 2 + t * ‖z + h‖ ^ 2))) := by
  have hrt : 0 < r + t := add_pos hr ht
  have hs (z : ℂ) := pairOverlap_gaussian_complete_square r t h z hrt.ne'
  simp_rw [hs, neg_add, Real.exp_add]
  have hg (z : ℂ) : Real.exp (-((r + t) * ‖z + (t / (r + t) : ℝ) • h‖ ^ 2)) =
      complexGaussian (r + t) (z + (t / (r + t) : ℝ) • h) := by
    unfold complexGaussian
    congr 1
    ring
  simp_rw [hg]
  exact ((complexGaussian_integrable hrt).comp_add_right
    ((t / (r + t) : ℝ) • h)).mul_const _

end UnitDistance
