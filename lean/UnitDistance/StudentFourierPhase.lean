module

public import UnitDistance.StudentFourierDecay

@[expose] public section
set_option backward.privateInPublic true


/-! Exact Fourier phase factors for justified horizontal contour shifts. -/

open MeasureTheory Filter Set
open scoped Topology

namespace UnitDistance.FourierContour

/-- The Fourier kernel with the exact `exp(-2*pi*i*xi*z)` convention. -/
noncomputable def fourierKernel (ξ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-((2*Real.pi*ξ:ℝ):ℂ)*Complex.I*z)

theorem norm_fourierKernel (ξ x y : ℝ) :
    ‖fourierKernel ξ ((x:ℂ)+(y:ℂ)*Complex.I)‖ = Real.exp (2*Real.pi*ξ*y) := by
  rw [fourierKernel, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem fourierKernel_add_imag (ξ x y : ℝ) :
    fourierKernel ξ ((x:ℂ)+(y:ℂ)*Complex.I) =
      (Real.exp (2*Real.pi*ξ*y):ℂ)*fourierKernel ξ (x:ℂ) := by
  unfold fourierKernel
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination -(2*(Real.pi:ℂ)*ξ*y)*(Complex.I_sq)

/-- A uniform phase bound on the whole strip, sufficient to retain the same
Student decay exponent during the rigorous contour truncation. -/
theorem norm_fourierKernel_le_strip (ξ x y a b : ℝ) (hy : y ∈ Set.uIcc a b) :
    ‖fourierKernel ξ ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤
      Real.exp (2*Real.pi*|ξ| *max |a| |b|) := by
  rw [norm_fourierKernel, Real.exp_le_exp]
  have hyabs : |y| ≤ max |a| |b| := by
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab] at hy
      exact abs_le_max_abs_abs hy.1 hy.2
    · rw [Set.uIcc_of_ge hba] at hy
      simpa only [max_comm] using abs_le_max_abs_abs hy.1 hy.2
  have hxy : ξ*y ≤ |ξ| *max |a| |b| := by
    calc
      ξ*y ≤ |ξ*y| := le_abs_self _
      _ = |ξ| *|y| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hyabs (abs_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hxy (by positivity : 0≤2*Real.pi)]

/-- The phase-weighted infinite contour equality, with the phase factor at
each height made explicit. Its hypotheses retain only ordinary holomorphy
and a pointwise Student bound on the unmodulated function. -/
theorem integral_fourier_shift_eq (f : ℂ → ℂ) (a b C r ξ : ℝ)
    (hC : 0 ≤ C) (hr : 1/2 < r)
    (hf : ∀ z : ℂ, z.im ∈ Set.uIcc a b → DifferentiableAt ℂ f z)
    (hbound : ∀ x y : ℝ, y ∈ Set.uIcc a b →
      ‖f ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤ C*(1+x^2)^(-r)) :
    (Real.exp (2*Real.pi*ξ*a):ℂ) *
      (∫ x : ℝ, f ((x:ℂ)+(a:ℂ)*Complex.I)*fourierKernel ξ (x:ℂ)) =
    (Real.exp (2*Real.pi*ξ*b):ℂ) *
      (∫ x : ℝ, f ((x:ℂ)+(b:ℂ)*Complex.I)*fourierKernel ξ (x:ℂ)) := by
  let M : ℝ := Real.exp (2*Real.pi*|ξ| *max |a| |b|)
  have hphase : Differentiable ℂ (fourierKernel ξ) := by unfold fourierKernel; fun_prop
  have h := integral_horizontal_shift_eq_of_student_decay
    (fun z => f z*fourierKernel ξ z) a b (C*M) r hr
    (fun z hz => (hf z hz).mul hphase.differentiableAt) (by
      intro x y hy
      rw [norm_mul]
      calc
        _ ≤ (C*(1+x^2)^(-r))*M := mul_le_mul (hbound x y hy)
          (norm_fourierKernel_le_strip ξ x y a b hy) (norm_nonneg _) (by positivity)
        _ = _ := by ring)
  have hid (x y : ℝ) : f ((x:ℂ)+(y:ℂ)*Complex.I)*fourierKernel ξ ((x:ℂ)+(y:ℂ)*Complex.I) =
      (Real.exp (2*Real.pi*ξ*y):ℂ)*(f ((x:ℂ)+(y:ℂ)*Complex.I)*fourierKernel ξ (x:ℂ)) := by
    rw [fourierKernel_add_imag]
    ring
  simp_rw [hid, integral_const_mul] at h
  exact h

end UnitDistance.FourierContour
