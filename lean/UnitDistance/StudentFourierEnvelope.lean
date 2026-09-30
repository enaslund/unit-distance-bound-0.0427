module

public import UnitDistance.StudentFourierShift
public import UnitDistance.StudentFourierDirection
public import Mathlib.Analysis.Fourier.FourierTransform

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual original Student Fourier envelope

The original noninteger `pairProfile^p` has the exact sum-of-coordinate-norms
Fourier decay, with its own independently defined mass and certified tube
constant. All contour and tube inputs are discharged in this theorem.
-/

open MeasureTheory FourierTransform

namespace UnitDistance.Witness

noncomputable def studentFourEuclideanCoordinates :
    (Fin 4 → ℝ) ≃ᵐ WithLp 2 (ℂ × ℂ) :=
  studentFourCoordinates.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).toHomeomorph.toMeasurableEquiv.symm

theorem studentFourEuclideanCoordinates_measurePreserving :
    MeasurePreserving studentFourEuclideanCoordinates volume volume := by
  have h : MeasurePreserving
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).toHomeomorph.toMeasurableEquiv volume volume :=
    WithLp.volume_preserving_ofLp ℂ ℂ
  exact (h.symm _).comp studentFourCoordinates_measurePreserving

@[simp] theorem studentFourEuclideanCoordinates_apply (x : Fin 4 → ℝ) :
    studentFourEuclideanCoordinates x = WithLp.toLp 2 (studentFourCoordinates x) := rfl

theorem studentFourKernel_frequency (ξ : WithLp 2 (ℂ × ℂ)) (x : Fin 4 → ℝ) :
    studentFourKernel (studentFourFrequency (WithLp.ofLp ξ)) x =
      Complex.exp (((-2*Real.pi*inner ℝ (studentFourEuclideanCoordinates x) ξ:ℝ):ℂ)*Complex.I) := by
  simp [studentFourKernel, studentFourFrequency, Fin.prod_univ_succ,
    FourierContour.fourierKernel, ← Complex.exp_add,
    studentFourEuclideanCoordinates_apply, WithLp.prod_inner_apply,
    real_inner_eq_re_inner ℂ, RCLike.inner_apply, studentFourCoordinates_apply,
    Complex.mul_re, Complex.mul_im]
  congr 1
  ring

theorem pairProfile_fourier_eq_studentFourIntegral (ξ : WithLp 2 (ℂ × ℂ)) :
    𝓕 (fun x : WithLp 2 (ℂ × ℂ) => ((pairProfile (WithLp.ofLp x)^p:ℝ):ℂ)) ξ =
      ∫ x, studentFourIntegrand 0 (studentFourFrequency (WithLp.ofLp ξ)) x := by
  rw [Real.fourier_eq']
  rw [← studentFourEuclideanCoordinates_measurePreserving.integral_comp']
  apply integral_congr_ae
  filter_upwards [] with x
  rw [studentFourIntegrand, studentFourKernel_frequency]
  have hw : studentFourWeight 0 x = ((pairProfile (studentFourCoordinates x)^p:ℝ):ℂ) := by
    simp only [studentFourWeight, studentFourPlanes_zero, complexPairWeight_real]
  rw [hw]
  simp only [studentFourEuclideanCoordinates_apply, WithLp.ofLp_toLp, smul_eq_mul, mul_comm]

/-- The original profile has the exact product-tube Fourier envelope, with
the published noninteger power, original mass, and certified tube constant. -/
theorem pairProfile_fourier_envelope (ξ : WithLp 2 (ℂ × ℂ)) :
    ‖𝓕 (fun x : WithLp 2 (ℂ × ℂ) => ((pairProfile (WithLp.ofLp x)^p:ℝ):ℂ)) ξ‖ ≤
      (fourierTubeConstant*pairMass)*
        Real.exp (-studentFourierSigma*(‖(WithLp.ofLp ξ).1‖+‖(WithLp.ofLp ξ).2‖)) := by
  let ζ := WithLp.ofLp ξ
  have hy := studentFourDirection_mem_tube ζ
  rw [pairProfile_fourier_eq_studentFourIntegral,
    studentFourIntegral_shift (studentFourDirection ζ) _ hy, studentFourDirection_phase]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-studentFourierSigma*(‖ζ.1‖+‖ζ.2‖))*
        (∫ x, ‖studentFourIntegrand (studentFourDirection ζ) (studentFourFrequency ζ) x‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
        (Real.exp_pos _).le
    _ ≤ Real.exp (-studentFourierSigma*(‖ζ.1‖+‖ζ.2‖))*(fourierTubeConstant*pairMass) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [norm_studentFourIntegrand] using integral_norm_studentFourWeight_le _ hy
    _ = _ := by ring

end UnitDistance.Witness
