module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Norm

@[expose] public section
set_option backward.privateInPublic true


/-!
# Complex Student denominators in the Euclidean tube

The denominator is the actual holomorphic quadratic `1+sum(z_i^2)`.
Its real part and norm are controlled after an imaginary Euclidean shift,
with the exact scale factor used by the manuscript.
-/

open scoped BigOperators RealInnerProductSpace

namespace UnitDistance.BernsteinTube

variable {ι : Type*} [Fintype ι]

noncomputable def studentDenominator (z : ι → ℂ) : ℂ := 1+∑ i, z i^2

noncomputable def complexShift (x y : EuclideanSpace ℝ ι) (i : ι) : ℂ :=
  (x i : ℂ)+Complex.I*(y i : ℂ)

omit [Fintype ι] in
@[simp] theorem complexShift_re (x y : EuclideanSpace ℝ ι) (i : ι) :
    (complexShift x y i).re = x i := by simp [complexShift]

omit [Fintype ι] in
@[simp] theorem complexShift_im (x y : EuclideanSpace ℝ ι) (i : ι) :
    (complexShift x y i).im = y i := by simp [complexShift]

theorem studentDenominator_re (x y : EuclideanSpace ℝ ι) :
    (studentDenominator (complexShift x y)).re = 1+‖x‖^2-‖y‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [studentDenominator, Complex.add_re, Complex.one_re, Complex.re_sum, sq,
    Complex.mul_re, complexShift_re, complexShift_im, Finset.sum_sub_distrib]
  ring

theorem studentDenominator_im (x y : EuclideanSpace ℝ ι) :
    (studentDenominator (complexShift x y)).im = 2*inner ℝ x y := by
  simp only [studentDenominator, Complex.add_im, Complex.one_im, Complex.im_sum, sq,
    Complex.mul_im, complexShift_re, complexShift_im, zero_add,
    PiLp.inner_apply, Real.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem studentDenominator_re_lower (x y : EuclideanSpace ℝ ι) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    (1-ρ^2)*(1+‖x‖^2) ≤ (studentDenominator (complexShift x y)).re := by
  rw [studentDenominator_re]
  nlinarith [sq_nonneg ‖x‖, mul_nonneg (sq_nonneg ρ) (sq_nonneg ‖x‖), norm_nonneg y]

theorem studentDenominator_re_pos (x y : EuclideanSpace ℝ ι) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hy : ‖y‖ ≤ ρ) :
    0 < (studentDenominator (complexShift x y)).re := by
  have hlow := studentDenominator_re_lower x y hρ0 hy
  have hfac : 0 < 1-ρ^2 := by nlinarith
  have hx : 0 < 1+‖x‖^2 := by positivity
  exact (mul_pos hfac hx).trans_le hlow

theorem studentDenominator_norm_lower (x y : EuclideanSpace ℝ ι) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    (1-ρ^2)*(1+‖x‖^2) ≤ ‖studentDenominator (complexShift x y)‖ :=
  (studentDenominator_re_lower x y hρ0 hy).trans (Complex.re_le_norm _)

/-- The imaginary shift changes the holomorphic quadratic by at most its
explicit linear and quadratic terms. -/
theorem studentDenominator_sub_real_norm_le (x y : EuclideanSpace ℝ ι) :
    ‖studentDenominator (complexShift x y) - ((1+‖x‖^2 : ℝ):ℂ)‖ ≤
      ‖y‖^2+2*‖x‖*‖y‖ := by
  have h := Complex.norm_le_abs_re_add_abs_im
    (studentDenominator (complexShift x y) - ((1+‖x‖^2 : ℝ):ℂ))
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    studentDenominator_re, studentDenominator_im, sub_zero] at h
  have heq : 1+‖x‖^2-‖y‖^2-(1+‖x‖^2) = -‖y‖^2 := by ring
  rw [heq, abs_neg, abs_of_nonneg (sq_nonneg _), abs_mul,
    abs_of_pos (show (0:ℝ)<2 by norm_num)] at h
  have hi := abs_real_inner_le_norm x y
  nlinarith

/-- The exact manuscript inverse-denominator radius follows from the ordinary
Euclidean shift bound. This is a statement about the actual complex reciprocal. -/
theorem studentDenominator_inv_sub_real_norm_le (x y : EuclideanSpace ℝ ι) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hy : ‖y‖ ≤ ρ) :
    ‖(studentDenominator (complexShift x y))⁻¹ -
      (((1+‖x‖^2)⁻¹ : ℝ):ℂ)‖ ≤ (ρ+ρ^2)/(1-ρ^2) := by
  let A : ℝ := 1+‖x‖^2
  let D : ℂ := studentDenominator (complexShift x y)
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg ‖x‖]
  have hδ : 0 < 1-ρ^2 := by nlinarith
  have hDre : 0 < D.re := studentDenominator_re_pos x y hρ0 hρ1 hy
  have hD : D ≠ 0 := by intro hz; simp [hz] at hDre
  have hDn : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hAc : (A:ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hnum := studentDenominator_sub_real_norm_le x y
  have hnum' : ‖D-(A:ℂ)‖ ≤ (ρ+ρ^2)*A := by
    dsimp [D, A]
    have hsq : ‖y‖^2 ≤ ρ^2 := by nlinarith [norm_nonneg y]
    have hlinear : 2*‖x‖*‖y‖ ≤ 2*‖x‖*ρ :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    have hx := mul_nonneg hρ0 (sq_nonneg (‖x‖-1))
    have hxx := mul_nonneg (sq_nonneg ρ) (sq_nonneg ‖x‖)
    nlinarith
  have hden : (1-ρ^2)*A ≤ ‖D‖ := studentDenominator_norm_lower x y hρ0 hy
  change ‖D - (A:ℂ)‖ ≤ _ at hnum'
  change ‖D⁻¹ - ((A⁻¹:ℝ):ℂ)‖ ≤ _
  rw [Complex.ofReal_inv, inv_sub_inv hD hAc, norm_div, norm_mul,
    norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
  apply (div_le_iff₀ (mul_pos hDn hA)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hδ).mpr
  have hbig : (ρ+ρ^2)*A ≤ (ρ+ρ^2)*A^2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hden (by positivity : 0 ≤ (ρ+ρ^2)*A)
  have hnumδ := mul_le_mul_of_nonneg_right (hnum'.trans hbig) hδ.le
  nlinarith

end UnitDistance.BernsteinTube
