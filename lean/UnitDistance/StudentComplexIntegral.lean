module

public import UnitDistance.StudentComplexMajorant

@[expose] public section
set_option backward.privateInPublic true


/-! Integrability and exact mass control of the actual holomorphic tube slices. -/

open MeasureTheory

namespace UnitDistance.Witness

theorem continuous_normalizedStudentPair_shift (y : StudentRealPlane × StudentRealPlane) :
    Continuous (fun z : ℂ × ℂ => pairComplexShift (normalizedStudentPair z) y) := by
  unfold pairComplexShift normalizedStudentPair complexToStudentRealPlane BernsteinTube.complexShift
  fun_prop

theorem continuous_complexPairWeight_shift (y : StudentRealPlane × StudentRealPlane)
    (hy1 : ‖y.1‖ ≤ 1/1000) (hy2 : ‖y.2‖ ≤ 1/1000) :
    Continuous (fun z : ℂ × ℂ => complexPairWeight (pairComplexShift (normalizedStudentPair z) y)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact ContinuousAt.comp (f := fun w : ℂ × ℂ => pairComplexShift (normalizedStudentPair w) y)
    (complexPairWeight_differentiableAt (normalizedStudentPair z) y hy1 hy2).continuousAt
    (continuous_normalizedStudentPair_shift y).continuousAt

/-- Every permitted shifted slice is genuinely Lebesgue integrable. -/
theorem integrable_complexPairWeight_shift (y : StudentRealPlane × StudentRealPlane)
    (hy1 : ‖y.1‖ ≤ 1/1000) (hy2 : ‖y.2‖ ≤ 1/1000) :
    Integrable (fun z : ℂ × ℂ => complexPairWeight (pairComplexShift (normalizedStudentPair z) y)) :=
  (integrable_pairMass.const_mul fourierTubeConstant).mono'
    (continuous_complexPairWeight_shift y hy1 hy2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => complexPairWeight_norm_le z y hy1 hy2))

/-- The full shifted absolute integral is bounded by the manuscript's exact
constant times the independently defined original mass `pairMass`. -/
theorem integral_norm_complexPairWeight_shift_le (y : StudentRealPlane × StudentRealPlane)
    (hy1 : ‖y.1‖ ≤ 1/1000) (hy2 : ‖y.2‖ ≤ 1/1000) :
    (∫ z : ℂ × ℂ, ‖complexPairWeight (pairComplexShift (normalizedStudentPair z) y)‖) ≤
      fourierTubeConstant * pairMass := by
  have h := integral_mono (integrable_complexPairWeight_shift y hy1 hy2).norm
    (integrable_pairMass.const_mul fourierTubeConstant)
    (fun z => complexPairWeight_norm_le z y hy1 hy2)
  simpa only [integral_const_mul, pairMass] using h

end UnitDistance.Witness
