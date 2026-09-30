module

public import UnitDistance.StudentFourierPhase

@[expose] public section
set_option backward.privateInPublic true


/-! Exact scalar normalization of the Fourier contour identity. -/

open MeasureTheory

namespace UnitDistance.FourierContour

theorem fourierKernel_div_mul (ξ c x : ℝ) (hc : c ≠ 0) :
    fourierKernel (ξ/c) ((c*x:ℝ):ℂ) = fourierKernel ξ (x:ℂ) := by
  unfold fourierKernel
  congr 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hc]

theorem integral_scaled_fourier (f : ℂ → ℂ) (a ξ c : ℝ) (hc : c ≠ 0) :
    (∫ x : ℝ, f ((c*x:ℝ)+(a:ℂ)*Complex.I)*fourierKernel ξ (x:ℂ)) =
      ((|c⁻¹|:ℝ):ℂ)*(∫ x : ℝ, f ((x:ℂ)+(a:ℂ)*Complex.I)*fourierKernel (ξ/c) (x:ℂ)) := by
  have h := Measure.integral_comp_mul_left
    (fun x : ℝ => f ((x:ℂ)+(a:ℂ)*Complex.I)*fourierKernel (ξ/c) (x:ℂ)) c
  simpa only [fourierKernel_div_mul ξ c _ hc, Complex.real_smul, smul_eq_mul] using h

theorem integral_fourier_shift_scaled {f : ℂ → ℂ} (a b ξ c : ℝ) (hc : c ≠ 0)
    (h : (Real.exp (2*Real.pi*(ξ/c)*a):ℂ)*
        (∫ x : ℝ, f ((x:ℂ)+(a:ℂ)*Complex.I)*fourierKernel (ξ/c) (x:ℂ)) =
      (Real.exp (2*Real.pi*(ξ/c)*b):ℂ)*
        (∫ x : ℝ, f ((x:ℂ)+(b:ℂ)*Complex.I)*fourierKernel (ξ/c) (x:ℂ))) :
    (Real.exp (2*Real.pi*(ξ/c)*a):ℂ)*
        (∫ x : ℝ, f ((c*x:ℝ)+(a:ℂ)*Complex.I)*fourierKernel ξ (x:ℂ)) =
      (Real.exp (2*Real.pi*(ξ/c)*b):ℂ)*
        (∫ x : ℝ, f ((c*x:ℝ)+(b:ℂ)*Complex.I)*fourierKernel ξ (x:ℂ)) := by
  rw [integral_scaled_fourier f a ξ c hc, integral_scaled_fourier f b ξ c hc]
  linear_combination ((|c⁻¹|:ℝ):ℂ)*h

end UnitDistance.FourierContour
