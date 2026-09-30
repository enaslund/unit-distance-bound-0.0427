module

public import UnitDistance.TsfasmanVladutKernel

@[expose] public section
set_option backward.privateInPublic true


/-!
# Boundary values of the Tsfasman–Vlăduţ transform

The actual even kernel cancels its hyperbolic denominator when the two
boundary transforms are added. The remaining bilateral exponential integral
is evaluated using Mathlib's improper complex exponential integrals.
-/

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate

namespace UnitDistance.NumberFieldAnalysis

@[simp] theorem tvKernel_conj (e x : ℝ) : conj (tvKernel e x) = tvKernel e x := by
  simp only [tvKernel, Complex.conj_ofReal]

theorem tvTransform_one_sub (e : ℝ) (s : ℂ) :
    tvTransform e (1-s) = tvTransform e s := by
  unfold tvTransform
  rw [← integral_neg_eq_self (fun x : ℝ => tvKernel e x * Complex.exp (((1-s)-1/2)*x)) volume]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [tvKernel_neg, Complex.ofReal_neg]
  congr 2
  ring

theorem tvTransform_conj (e : ℝ) (s : ℂ) :
    tvTransform e (conj s) = conj (tvTransform e s) := by
  unfold tvTransform
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_mul, tvKernel_conj, ← Complex.exp_conj, map_sub, map_div₀, map_one,
    map_ofNat, Complex.conj_ofReal]

/-- The bilateral exponential transform, with its actual value in `ℂ`. -/
theorem tv_integral_exp_neg_abs_fourier {e : ℝ} (he : 0 < e) (t : ℝ) :
    (∫ x : ℝ, (Real.exp (-e*|x|) : ℂ)*Complex.exp (((t:ℂ)*I)*x)) =
      ((2*e/(e^2+t^2) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun x => (Real.exp (-e*|x|) : ℂ)*Complex.exp (((t:ℂ)*I)*x)
  have hf : Integrable f := by
    apply (tv_integrable_exp_neg_abs he).mono'
    · exact (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_abs))).mul
          ((continuous_const.mul Complex.continuous_ofReal).cexp) |>.aestronglyMeasurable
    · filter_upwards [] with x
      simp [f, Complex.norm_exp]
  have hn : (∫ x : ℝ in Iic 0, f x) = 1/((e:ℂ)+(t:ℂ)*I) := by
    rw [setIntegral_congr_fun measurableSet_Iic (fun x hx =>
      show f x = Complex.exp (((e:ℂ)+(t:ℂ)*I)*x) by
        simp only [f, abs_of_nonpos (show x ≤ 0 from hx), Complex.ofReal_exp, Complex.ofReal_mul,
          Complex.ofReal_neg, ← Complex.exp_add]
        congr 1
        ring)]
    simpa using integral_exp_mul_complex_Iic (a := (e:ℂ)+(t:ℂ)*I) (by simpa using he) 0
  have hp : (∫ x : ℝ in Ioi 0, f x) = -1/(-(e:ℂ)+(t:ℂ)*I) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx =>
      show f x = Complex.exp ((-(e:ℂ)+(t:ℂ)*I)*x) by
        simp only [f, abs_of_pos (show 0 < x from hx), Complex.ofReal_exp, Complex.ofReal_mul,
          Complex.ofReal_neg, ← Complex.exp_add]
        congr 1
        ring)]
    simpa using integral_exp_mul_complex_Ioi (a := -(e:ℂ)+(t:ℂ)*I) (by simp; linarith) 0
  change (∫ x : ℝ, f x) = _
  rw [← integral_add_compl measurableSet_Iic hf, compl_Iic, hn, hp]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, Complex.normSq_apply,
      zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, sub_zero,
      neg_zero, neg_neg, neg_mul, mul_neg, neg_div] <;> ring

/-- Exact cancellation of the cosh denominator between both boundary integrands. -/
theorem tvIntegrand_boundary_add (e t x : ℝ) :
    tvKernel e x*Complex.exp (((1:ℂ)+(t:ℂ)*I-1/2)*x) +
      tvKernel e x*Complex.exp (((t:ℂ)*I-1/2)*x) =
    2*((Real.exp (-e*|x|) : ℂ)*Complex.exp (((t:ℂ)*I)*x)) := by
  have h₁ : (((1:ℂ)+(t:ℂ)*I-1/2)*(x:ℂ)) =
      ((x/2:ℝ):ℂ)+((t:ℂ)*I)*x := by push_cast; ring
  have h₀ : (((t:ℂ)*I-1/2)*(x:ℂ)) =
      ((-(x/2):ℝ):ℂ)+((t:ℂ)*I)*x := by push_cast; ring
  rw [h₁, h₀, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  have hc : (Real.exp (x/2) : ℂ)+(Real.exp (-(x/2)) : ℂ) =
      2*(Real.cosh (x/2) : ℂ) := by
    norm_cast
    rw [Real.cosh_eq]
    ring
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ← mul_add, hc]
  have hcn : (Real.cosh (x/2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  unfold tvKernel
  rw [Complex.ofReal_div]
  field_simp [hcn]

theorem tvTransform_boundary_add {e : ℝ} (he : 0 < e) (t : ℝ) :
    tvTransform e (1+(t:ℂ)*I)+tvTransform e ((t:ℂ)*I) =
      ((4*e/(e^2+t^2) : ℝ) : ℂ) := by
  have h₁ : |(1+(t:ℂ)*I).re-1/2| < 1/2+e := by norm_num; linarith
  have h₀ : |((t:ℂ)*I).re-1/2| < 1/2+e := by norm_num; linarith
  unfold tvTransform
  rw [← integral_add (integrable_tvIntegrand h₁) (integrable_tvIntegrand h₀)]
  simp_rw [tvIntegrand_boundary_add]
  rw [integral_const_mul, tv_integral_exp_neg_abs_fourier he]
  push_cast
  ring

theorem tvTransform_re_one_add_mul_I {e : ℝ} (he : 0 < e) (t : ℝ) :
    (tvTransform e (1+(t:ℂ)*I)).re = 2*e/(e^2+t^2) := by
  have hs : tvTransform e ((t:ℂ)*I) = conj (tvTransform e (1+(t:ℂ)*I)) := by
    rw [← tvTransform_conj, ← tvTransform_one_sub e (conj (1+(t:ℂ)*I))]
    congr 1
    simp
  have h := congrArg Complex.re (tvTransform_boundary_add he t)
  rw [hs, Complex.add_re, Complex.conj_re, Complex.ofReal_re] at h
  linear_combination h / 2

theorem tvTransform_re_mul_I {e : ℝ} (he : 0 < e) (t : ℝ) :
    (tvTransform e ((t:ℂ)*I)).re = 2*e/(e^2+t^2) := by
  have h := congrArg Complex.re (tvTransform_boundary_add he t)
  rw [Complex.add_re, Complex.ofReal_re, tvTransform_re_one_add_mul_I he] at h
  linear_combination h

end UnitDistance.NumberFieldAnalysis
