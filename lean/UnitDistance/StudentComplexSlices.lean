module

public import UnitDistance.StudentComplexDecay
public import UnitDistance.StudentFourierPhase

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual one-coordinate Student contours

The scalar slice is an actual coordinate restriction of the published complex
extension. Its holomorphy and polynomial decay are proved here, so the contour
identity has only geometric tube membership as an input.
-/

open MeasureTheory Set

namespace UnitDistance.Witness

noncomputable def studentRealPlaneUpdate (x : StudentRealPlane) (i : Fin 2) (t : ℝ) :
    StudentRealPlane := WithLp.toLp 2 (Function.update x i t)

theorem studentComplexPlaneImag_update (z : StudentComplexPlane) (i : Fin 2) (w : ℂ) :
    studentComplexPlaneImag (Function.update z i w) =
      studentRealPlaneUpdate (studentComplexPlaneImag z) i w.im := by
  ext j
  by_cases hji : j=i <;>
    simp [studentComplexPlaneImag, studentRealPlaneUpdate, Function.update, hji]

noncomputable def complexPairWeightFstSlice (z : StudentComplexPlane × StudentComplexPlane)
    (i : Fin 2) (w : ℂ) : ℂ := complexPairWeight (Function.update z.1 i w, z.2)

noncomputable def complexPairWeightSndSlice (z : StudentComplexPlane × StudentComplexPlane)
    (i : Fin 2) (w : ℂ) : ℂ := complexPairWeight (z.1, Function.update z.2 i w)

private theorem differentiable_update (z : StudentComplexPlane) (i : Fin 2) :
    Differentiable ℂ (fun w : ℂ => Function.update z i w) := by
  intro w
  apply differentiableAt_pi.mpr
  intro j
  by_cases hji : j=i
  · simp [Function.update, hji]
  · simp [Function.update, hji]

/-- Holomorphy of the actual scalar slice, with no analytic assumption. -/
theorem complexPairWeightFstSlice_differentiableAt
    (z : StudentComplexPlane × StudentComplexPlane) (i : Fin 2) (w : ℂ)
    (hw : ‖studentRealPlaneUpdate (studentComplexPlaneImag z.1) i w.im‖ ≤ 1/1000)
    (hz2 : ‖studentComplexPlaneImag z.2‖ ≤ 1/1000) :
    DifferentiableAt ℂ (complexPairWeightFstSlice z i) w := by
  have hdiff := complexPairWeight_differentiableAt_of_mem_tube (Function.update z.1 i w, z.2)
    (by exact ⟨by simpa only [studentComplexPlaneImag_update] using hw, hz2⟩)
  exact hdiff.comp w ((differentiable_update z.1 i).differentiableAt.prodMk (differentiableAt_const z.2))

theorem complexPairWeightSndSlice_differentiableAt
    (z : StudentComplexPlane × StudentComplexPlane) (i : Fin 2) (w : ℂ)
    (hz1 : ‖studentComplexPlaneImag z.1‖ ≤ 1/1000)
    (hw : ‖studentRealPlaneUpdate (studentComplexPlaneImag z.2) i w.im‖ ≤ 1/1000) :
    DifferentiableAt ℂ (complexPairWeightSndSlice z i) w := by
  have hdiff := complexPairWeight_differentiableAt_of_mem_tube (z.1, Function.update z.2 i w)
    (by exact ⟨hz1, by simpa only [studentComplexPlaneImag_update] using hw⟩)
  exact hdiff.comp w ((differentiableAt_const z.1).prodMk (differentiable_update z.2 i).differentiableAt)

/-- Actual scalar Student decay of the first-plane slice throughout its tube. -/
theorem complexPairWeightFstSlice_norm_le
    (z : StudentComplexPlane × StudentComplexPlane) (i : Fin 2) (x y : ℝ)
    (hy : ‖studentRealPlaneUpdate (studentComplexPlaneImag z.1) i y‖ ≤ 1/1000)
    (hz2 : ‖studentComplexPlaneImag z.2‖ ≤ 1/1000) :
    ‖complexPairWeightFstSlice z i ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤
      (fourierTubeConstant*14^p)*(1+x^2)^(-(s*p)) := by
  let u : StudentComplexPlane := Function.update z.1 i ((x:ℂ)+(y:ℂ)*Complex.I)
  have hu : ‖studentComplexPlaneImag u‖ ≤ 1/1000 := by
    simpa [u, studentComplexPlaneImag_update] using hy
  have h := complexPairWeight_fst_coordinate_norm_le
    (studentComplexPlaneReal u, studentComplexPlaneReal z.2)
    (studentComplexPlaneImag u, studentComplexPlaneImag z.2) i hu hz2
  dsimp only [pairComplexShift] at h
  rw [complexShift_real_imag, complexShift_real_imag] at h
  simpa [complexPairWeightFstSlice, studentComplexPlaneReal, u, neg_mul] using h

theorem complexPairWeightSndSlice_norm_le
    (z : StudentComplexPlane × StudentComplexPlane) (i : Fin 2) (x y : ℝ)
    (hz1 : ‖studentComplexPlaneImag z.1‖ ≤ 1/1000)
    (hy : ‖studentRealPlaneUpdate (studentComplexPlaneImag z.2) i y‖ ≤ 1/1000) :
    ‖complexPairWeightSndSlice z i ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤
      (fourierTubeConstant*14^p)*(1+x^2)^(-(s*p)) := by
  let u : StudentComplexPlane := Function.update z.2 i ((x:ℂ)+(y:ℂ)*Complex.I)
  have hu : ‖studentComplexPlaneImag u‖ ≤ 1/1000 := by
    simpa [u, studentComplexPlaneImag_update] using hy
  have h := complexPairWeight_snd_coordinate_norm_le
    (studentComplexPlaneReal z.1, studentComplexPlaneReal u)
    (studentComplexPlaneImag z.1, studentComplexPlaneImag u) i hz1 hu
  dsimp only [pairComplexShift] at h
  rw [complexShift_real_imag, complexShift_real_imag] at h
  simpa [complexPairWeightSndSlice, studentComplexPlaneReal, u, neg_mul] using h

/-- The actual first-plane coordinate contour, including the exact Fourier
phase factors. The only assumptions specify the allowed imaginary tube. -/
theorem complexPairWeightFstSlice_fourier_shift
    (z : StudentComplexPlane × StudentComplexPlane) (i : Fin 2) (a₀ b₀ ξ : ℝ)
    (hstrip : ∀ y ∈ Set.uIcc a₀ b₀,
      ‖studentRealPlaneUpdate (studentComplexPlaneImag z.1) i y‖ ≤ 1/1000)
    (hz2 : ‖studentComplexPlaneImag z.2‖ ≤ 1/1000) :
    (Real.exp (2*Real.pi*ξ*a₀):ℂ) *
      (∫ x : ℝ, complexPairWeightFstSlice z i ((x:ℂ)+(a₀:ℂ)*Complex.I)*
        FourierContour.fourierKernel ξ (x:ℂ)) =
    (Real.exp (2*Real.pi*ξ*b₀):ℂ) *
      (∫ x : ℝ, complexPairWeightFstSlice z i ((x:ℂ)+(b₀:ℂ)*Complex.I)*
        FourierContour.fourierKernel ξ (x:ℂ)) := by
  have hq : (0:ℝ) ≤ (fourierTubeLoss:ℝ) := by exact_mod_cast fourierTubeLoss_nonneg
  apply FourierContour.integral_fourier_shift_eq (complexPairWeightFstSlice z i)
    a₀ b₀ (fourierTubeConstant*14^p) (s*p) ξ
    (by unfold fourierTubeConstant; positivity)
    (by linarith [exponent_student_integrable])
  · intro w hw
    exact complexPairWeightFstSlice_differentiableAt z i w (hstrip w.im hw) hz2
  · intro x y hy
    exact complexPairWeightFstSlice_norm_le z i x y (hstrip y hy) hz2

theorem complexPairWeightSndSlice_fourier_shift
    (z : StudentComplexPlane × StudentComplexPlane) (i : Fin 2) (a₀ b₀ ξ : ℝ)
    (hz1 : ‖studentComplexPlaneImag z.1‖ ≤ 1/1000)
    (hstrip : ∀ y ∈ Set.uIcc a₀ b₀,
      ‖studentRealPlaneUpdate (studentComplexPlaneImag z.2) i y‖ ≤ 1/1000) :
    (Real.exp (2*Real.pi*ξ*a₀):ℂ) *
      (∫ x : ℝ, complexPairWeightSndSlice z i ((x:ℂ)+(a₀:ℂ)*Complex.I)*
        FourierContour.fourierKernel ξ (x:ℂ)) =
    (Real.exp (2*Real.pi*ξ*b₀):ℂ) *
      (∫ x : ℝ, complexPairWeightSndSlice z i ((x:ℂ)+(b₀:ℂ)*Complex.I)*
        FourierContour.fourierKernel ξ (x:ℂ)) := by
  have hq : (0:ℝ) ≤ (fourierTubeLoss:ℝ) := by exact_mod_cast fourierTubeLoss_nonneg
  apply FourierContour.integral_fourier_shift_eq (complexPairWeightSndSlice z i)
    a₀ b₀ (fourierTubeConstant*14^p) (s*p) ξ
    (by unfold fourierTubeConstant; positivity)
    (by linarith [exponent_student_integrable])
  · intro w hw
    exact complexPairWeightSndSlice_differentiableAt z i w hz1 (hstrip w.im hw)
  · intro x y hy
    exact complexPairWeightSndSlice_norm_le z i x y hz1 (hstrip y hy)

end UnitDistance.Witness
