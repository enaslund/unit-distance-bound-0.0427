module

public import UnitDistance.StudentSchwartzApproximation
public import Mathlib.Analysis.Fourier.Convolution

@[expose] public section
set_option backward.privateInPublic true


/-!
# Fourier convolution under genuine Schwartz regularization

Multiplication by a Schwartz function is Fourier convolution even when the
original weight is only integrable. The quantitative envelope estimate uses
an explicitly defined exponential moment of the convolution kernel.
-/

open MeasureTheory Filter FourierTransform
open scoped Topology RealInnerProductSpace

namespace UnitDistance

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem fourier_modulation (f : V → ℂ) (ξ y : V) :
    𝓕 (fun x => Real.fourierChar (-inner ℝ x ξ) • f x) y = 𝓕 f (ξ+y) := by
  simp only [Real.fourier_eq, inner_add_right, neg_add, AddChar.map_add_eq_mul, mul_smul]
  congr 1
  funext x
  exact smul_comm _ _ _

/-- This identity needs no Fourier integrability assumption on the original
weight: its L¹ integrability and the Schwartz multiplier suffice. -/
theorem fourier_mul_schwartz_eq_integral {f : V → ℂ} (hf : Integrable f)
    (g : SchwartzMap V ℂ) (ξ : V) :
    𝓕 (fun x => f x*g x) ξ = ∫ y, 𝓕 f (ξ-y) * 𝓕 g y := by
  let fm : V → ℂ := fun x => Real.fourierChar (-inner ℝ x ξ) • f x
  have hfm : Integrable fm := (Real.fourierIntegral_convergent_iff ξ).mpr hf
  have hp : (∫ y, 𝓕 fm y * (𝓕⁻ g) y) = ∫ x, fm x * g x := by
    have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner hfm ((𝓕⁻ g).integrable (μ := volume))
    have hinner : (innerₗ V).flip = innerₗ V := by ext x y; exact real_inner_comm x y
    rw [hinner] at h
    change (∫ y, 𝓕 fm y * (𝓕⁻ g) y) = ∫ x, fm x * 𝓕 (((𝓕⁻ g) : SchwartzMap V ℂ) : V → ℂ) x at h
    simpa only [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq] using h
  calc
    _ = ∫ x, fm x * g x := by
      simp only [Real.fourier_eq, fm, Circle.smul_def, smul_eq_mul, mul_assoc]
    _ = ∫ y, 𝓕 f (ξ+y) * (𝓕⁻ g) y := by
      rw [← hp]
      simp_rw [fm, fourier_modulation]
    _ = ∫ y, 𝓕 f (ξ-y) * (𝓕⁻ g) (-y) := by
      simpa only [sub_eq_add_neg] using
        (integral_neg_eq_self (fun y => 𝓕 f (ξ+y) * (𝓕⁻ g) y) volume).symm
    _ = _ := by
      congr 1
      funext y
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg,
        ← SchwartzMap.fourier_coe]

/-- The triangle inequality transfers an exponential envelope through a
positive convolution kernel. Its loss is the actual exponential norm
moment of that kernel. -/
theorem convolution_exponential_envelope
    {F : V → ℂ} {K : V → ℝ} {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hF : AEStronglyMeasurable F volume) (hK : AEStronglyMeasurable K volume)
    (hKpos : ∀ y, 0 ≤ K y)
    (hbound : ∀ y, ‖F y‖ ≤ C*Real.exp (-σ*‖y‖))
    (hMoment : Integrable (fun y => K y*Real.exp (σ*‖y‖))) (ξ : V) :
    ‖∫ y, F (ξ-y) * (K y : ℂ)‖ ≤
      C*Real.exp (-σ*‖ξ‖) * (∫ y, K y*Real.exp (σ*‖y‖)) := by
  have hpoint (y : V) : ‖F (ξ-y) * (K y : ℂ)‖ ≤
      (C*Real.exp (-σ*‖ξ‖)) * (K y*Real.exp (σ*‖y‖)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hKpos y)]
    calc
      _ ≤ (C*Real.exp (-σ*‖ξ-y‖))*K y := mul_le_mul_of_nonneg_right (hbound _) (hKpos y)
      _ ≤ (C*(Real.exp (-σ*‖ξ‖)*Real.exp (σ*‖y‖)))*K y := by
        apply mul_le_mul_of_nonneg_right ?_ (hKpos y)
        apply mul_le_mul_of_nonneg_left ?_ hC
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have htri : ‖ξ‖ ≤ ‖ξ-y‖+‖y‖ := by simpa using norm_add_le (ξ-y) y
        nlinarith [mul_le_mul_of_nonneg_left htri hσ]
      _ = _ := by ring
  have hm : AEStronglyMeasurable (fun y => F (ξ-y)*(K y : ℂ)) volume := by
    exact (hF.comp_measurePreserving (volume.measurePreserving_sub_left ξ)).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hK)
  have hi : Integrable (fun y => F (ξ-y)*(K y : ℂ)) :=
    (hMoment.const_mul (C*Real.exp (-σ*‖ξ‖))).mono' hm (Filter.Eventually.of_forall hpoint)
  calc
    _ ≤ ∫ y, ‖F (ξ-y)*(K y : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (C*Real.exp (-σ*‖ξ‖))*(K y*Real.exp (σ*‖y‖)) :=
      integral_mono hi.norm (hMoment.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

/-- Preservation of the specified seminorm envelope, including the
manuscript's sum of complex-coordinate norms. Euclidean norm is used only
to dominate the Gaussian's moment; it does not replace the envelope norm. -/
theorem convolution_seminorm_exponential_envelope
    (q : Seminorm ℝ V) {B : ℝ} (hq : ∀ y, q y ≤ B*‖y‖)
    {F : V → ℂ} {K : V → ℝ} {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hF : AEStronglyMeasurable F volume) (hK : AEStronglyMeasurable K volume)
    (hKpos : ∀ y, 0 ≤ K y)
    (hbound : ∀ y, ‖F y‖ ≤ C*Real.exp (-σ*q y))
    (hMoment : Integrable (fun y => K y*Real.exp ((σ*B)*‖y‖))) (ξ : V) :
    ‖∫ y, F (ξ-y) * (K y : ℂ)‖ ≤
      C*Real.exp (-σ*q ξ) * (∫ y, K y*Real.exp ((σ*B)*‖y‖)) := by
  have hpoint (y : V) : ‖F (ξ-y) * (K y : ℂ)‖ ≤
      (C*Real.exp (-σ*q ξ)) * (K y*Real.exp ((σ*B)*‖y‖)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hKpos y)]
    calc
      _ ≤ (C*Real.exp (-σ*q (ξ-y)))*K y :=
        mul_le_mul_of_nonneg_right (hbound _) (hKpos y)
      _ ≤ (C*(Real.exp (-σ*q ξ)*Real.exp ((σ*B)*‖y‖)))*K y := by
        apply mul_le_mul_of_nonneg_right ?_ (hKpos y)
        apply mul_le_mul_of_nonneg_left ?_ hC
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have htri : q ξ ≤ q (ξ-y)+q y := by simpa using map_add_le_add q (ξ-y) y
        nlinarith [mul_le_mul_of_nonneg_left htri hσ,
          mul_le_mul_of_nonneg_left (hq y) hσ]
      _ = _ := by ring
  have hm : AEStronglyMeasurable (fun y => F (ξ-y)*(K y : ℂ)) volume :=
    (hF.comp_measurePreserving (volume.measurePreserving_sub_left ξ)).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hK)
  have hi : Integrable (fun y => F (ξ-y)*(K y : ℂ)) :=
    (hMoment.const_mul (C*Real.exp (-σ*q ξ))).mono' hm (Filter.Eventually.of_forall hpoint)
  calc
    _ ≤ ∫ y, ‖F (ξ-y)*(K y : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (C*Real.exp (-σ*q ξ))*(K y*Real.exp ((σ*B)*‖y‖)) :=
      integral_mono hi.norm (hMoment.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

end UnitDistance
