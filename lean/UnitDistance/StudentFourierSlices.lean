module

public import UnitDistance.StudentFourierIntegrand
public import UnitDistance.StudentFourierFubini

@[expose] public section
set_option backward.privateInPublic true


/-! The actual scalar contours, transferred to ordinary four real coordinates. -/

open MeasureTheory

namespace UnitDistance.Witness

@[simp] private theorem update_two_zero (a b t : ℝ) :
    Function.update ![a,b] (0:Fin 2) t = ![t,b] := by
  funext i
  fin_cases i <;> simp

@[simp] private theorem update_two_one (a b t : ℝ) :
    Function.update ![a,b] (1:Fin 2) t = ![a,t] := by
  funext i
  fin_cases i <;> simp

noncomputable def studentFourPoint (x y : Fin 4 → ℝ) :
    StudentComplexPlane × StudentComplexPlane :=
  pairComplexShift (normalizedStudentPair (studentFourCoordinates x)) (studentFourPlanes y)

noncomputable def studentFourSlice (z : StudentComplexPlane × StudentComplexPlane)
    (i : Fin 4) : ℂ → ℂ :=
  ![complexPairWeightFstSlice z 0, complexPairWeightFstSlice z 1,
    complexPairWeightSndSlice z 0, complexPairWeightSndSlice z 1] i

theorem studentFourWeight_update (x y : Fin 4 → ℝ) (i : Fin 4) (t u : ℝ) :
    studentFourWeight (Function.update y i u) (Function.update x i t) =
      studentFourSlice (studentFourPoint x y) i
        ((Real.sqrt a*t:ℝ)+(u:ℂ)*Complex.I) := by
  fin_cases i <;>
    simp only [studentFourSlice, studentFourWeight, studentFourPoint]
  all_goals
    congr 1
    apply Prod.ext <;> ext j <;> fin_cases j <;>
      simp [pairComplexShift, normalizedStudentPair, studentFourCoordinates_apply,
        studentFourPlanes, complexToStudentRealPlane, BernsteinTube.complexShift,
        Function.update, Complex.mul_re, Complex.mul_im, mul_comm]

theorem studentFourSlice_fourier_shift (x y : Fin 4 → ℝ) (i : Fin 4) (u v ξ : ℝ)
    (hu : studentFourTube (Function.update y i u))
    (hv : studentFourTube (Function.update y i v)) :
    (Real.exp (2*Real.pi*ξ*u):ℂ)*
      (∫ t : ℝ, studentFourSlice (studentFourPoint x y) i
        ((t:ℂ)+(u:ℂ)*Complex.I)*FourierContour.fourierKernel ξ (t:ℂ)) =
    (Real.exp (2*Real.pi*ξ*v):ℂ)*
      (∫ t : ℝ, studentFourSlice (studentFourPoint x y) i
        ((t:ℂ)+(v:ℂ)*Complex.I)*FourierContour.fourierKernel ξ (t:ℂ)) := by
  fin_cases i
  · apply complexPairWeightFstSlice_fourier_shift_of_endpoints
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hu.1
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hv.1
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hu.2
  · apply complexPairWeightFstSlice_fourier_shift_of_endpoints
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hu.1
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hv.1
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hu.2
  · apply complexPairWeightSndSlice_fourier_shift_of_endpoints
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hu.1
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hu.2
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hv.2
  · apply complexPairWeightSndSlice_fourier_shift_of_endpoints
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hu.1
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hu.2
    · simpa [studentFourPoint, pairComplexShift, studentComplexPlaneImag,
        BernsteinTube.complexShift, studentRealPlaneUpdate, studentFourTube,
        studentFourPlanes, Function.update] using hv.2

theorem studentFourIntegrand_coordinate_shift (x y ξ : Fin 4 → ℝ) (i : Fin 4)
    (hy : studentFourTube y) :
    (∫ t : ℝ, studentFourIntegrand (Function.update y i 0) ξ (Function.update x i t)) =
      (Real.exp (2*Real.pi*(ξ i/Real.sqrt a)*y i):ℂ)*
        (∫ t : ℝ, studentFourIntegrand y ξ (Function.update x i t)) := by
  have hc : Real.sqrt a ≠ 0 := Real.sqrt_ne_zero'.mpr witness_basic.2.1
  have hs := FourierContour.integral_fourier_shift_scaled 0 (y i) (ξ i) (Real.sqrt a) hc
    (studentFourSlice_fourier_shift x y i 0 (y i) (ξ i/Real.sqrt a)
      (studentFourTube_update_zero hy i) (by simpa using hy))
  simp only [mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul,
    ← studentFourWeight_update, Function.update_eq_self] at hs
  have hfactor (v : Fin 4 → ℝ) :
      (∫ t : ℝ, studentFourIntegrand v ξ (Function.update x i t)) =
        studentFourKernel ξ (Function.update x i 0)*
          (∫ t : ℝ, studentFourWeight v (Function.update x i t)*
            FourierContour.fourierKernel (ξ i) (t:ℂ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [studentFourIntegrand, studentFourKernel_update]
    ring
  rw [hfactor, hfactor, hs]
  ring

theorem studentFourIntegral_coordinate_shift (y ξ : Fin 4 → ℝ) (i : Fin 4)
    (hy : studentFourTube y) :
    (∫ x, studentFourIntegrand (Function.update y i 0) ξ x) =
      (Real.exp (2*Real.pi*(ξ i/Real.sqrt a)*y i):ℂ)*
        (∫ x, studentFourIntegrand y ξ x) := by
  apply FourierContour.integral_eq_const_mul_of_coordinate
    (integrable_studentFourIntegrand _ _ (studentFourTube_update_zero hy i))
    (integrable_studentFourIntegrand _ _ hy) i
  intro x
  exact studentFourIntegrand_coordinate_shift x y ξ i hy

end UnitDistance.Witness
