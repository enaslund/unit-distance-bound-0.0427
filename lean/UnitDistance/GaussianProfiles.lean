module

public import UnitDistance.Witness
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual Gaussian compact-place integrals

All integrals use ordinary Lebesgue measure on the complex plane. Completing
the square computes the displacement-one overlap and proves its integrability.
The final identities specialize to the independently defined published witness.
-/

open MeasureTheory

namespace UnitDistance

noncomputable def complexGaussian (b : ℝ) (z : ℂ) : ℝ := Real.exp (-b * ‖z‖^2)

theorem complexGaussian_integrable {b : ℝ} (hb : 0 < b) : Integrable (complexGaussian b) := by
  change Integrable (fun z : ℂ => Real.exp (-b * ‖z‖^2))
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (b : ℂ)) (by simpa using hb) 0 0).re
  simpa [complexGaussian, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp] using h

theorem complexGaussian_integral {b : ℝ} (hb : 0 < b) :
    (∫ z : ℂ, complexGaussian b z) = Real.pi / b := by
  simpa [complexGaussian, Complex.finrank_real_complex] using
    GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) hb

theorem complexGaussian_power (b p : ℝ) (z : ℂ) :
    complexGaussian b z ^ p = complexGaussian (b*p) z := by
  rw [complexGaussian, ← Real.exp_mul, complexGaussian]
  congr 1
  ring

theorem complexGaussian_moment_integrable {b p : ℝ} (hb : 0 < b) (hp : 0 < p) :
    Integrable (fun z => complexGaussian b z ^ p) := by
  simp_rw [complexGaussian_power]
  exact complexGaussian_integrable (mul_pos hb hp)

theorem complexGaussian_moment {b p : ℝ} (hb : 0 < b) (hp : 0 < p) :
    (∫ z : ℂ, complexGaussian b z ^ p) = Real.pi / (b*p) := by
  simp_rw [complexGaussian_power]
  exact complexGaussian_integral (mul_pos hb hp)

theorem complex_complete_square (z : ℂ) :
    ‖z‖^2 + ‖z+1‖^2 = 2*‖z+(1/2 : ℂ)‖^2 + 1/2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im]
  norm_num
  ring

theorem complexGaussian_overlap_integrand (b : ℝ) (z : ℂ) :
    complexGaussian b z * complexGaussian b (z+1) =
      Real.exp (-b/2) * complexGaussian (2*b) (z+(1/2 : ℂ)) := by
  simp only [complexGaussian, ← Real.exp_add]
  congr 1
  have h := complex_complete_square z
  linear_combination -b * h

theorem complexGaussian_overlap_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : ℂ => complexGaussian b z * complexGaussian b (z+1)) := by
  simp_rw [complexGaussian_overlap_integrand]
  have hg := complexGaussian_integrable (b := 2*b) (by positivity)
  have h := ((measurePreserving_add_right (volume : Measure ℂ) (1/2 : ℂ)).integrable_comp
    hg.aestronglyMeasurable).mpr hg
  exact h.const_mul _

theorem complexGaussian_overlap {b : ℝ} (hb : 0 < b) :
    (∫ z : ℂ, complexGaussian b z * complexGaussian b (z+1)) =
      Real.exp (-b/2) * (Real.pi/(2*b)) := by
  simp_rw [complexGaussian_overlap_integrand]
  rw [integral_const_mul, integral_add_right_eq_self, complexGaussian_integral (by positivity)]

namespace Witness

theorem compactProfile_gaussian (z : ℂ) : compactProfile z = complexGaussian (2*increment) z := by
  simp only [compactProfile, aCompact, complexGaussian]
  congr 1
  have hp : p ≠ 0 := ne_of_gt witness_basic.2.2.1
  field_simp

theorem compactMass_integrable : Integrable (fun z : ℂ => compactProfile z ^ p) := by
  simp_rw [compactProfile_gaussian]
  exact complexGaussian_moment_integrable (by positivity [increment_pos]) witness_basic.2.2.1

theorem compactOverlap_integrable :
    Integrable (fun z : ℂ => compactProfile z * compactProfile (z+1)) := by
  simp_rw [compactProfile_gaussian]
  exact complexGaussian_overlap_integrable (by positivity [increment_pos])

theorem compactMass_eq : compactMass = Real.pi / (2*increment*p) := by
  simp only [compactMass, compactProfile_gaussian]
  exact complexGaussian_moment (by positivity [increment_pos]) witness_basic.2.2.1

theorem compactOverlap_eq : compactOverlap = Real.exp (-increment) * (Real.pi/(4*increment)) := by
  simp only [compactOverlap, compactProfile_gaussian]
  rw [complexGaussian_overlap (by positivity [increment_pos])]
  congr 1 <;> congr 1 <;> ring

theorem compactMass_pos : 0 < compactMass := by
  rw [compactMass_eq]
  positivity [increment_pos, witness_basic.2.2.1]

theorem compactOverlap_pos : 0 < compactOverlap := by
  rw [compactOverlap_eq]
  positivity [increment_pos, Real.pi_pos]

theorem JCompact_eq : JCompact =
    -increment + Real.log (Real.pi/(4*increment)) -
      (1+increment)*Real.log (Real.pi/(2*increment*p)) := by
  rw [JCompact, compactMass_eq, compactOverlap_eq,
    Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (by positivity [increment_pos, Real.pi_pos])),
    Real.log_exp]

end Witness

end UnitDistance
