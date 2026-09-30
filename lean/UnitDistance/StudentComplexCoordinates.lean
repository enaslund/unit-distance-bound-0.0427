module

public import UnitDistance.StudentComplexIntegral

@[expose] public section
set_option backward.privateInPublic true


/-! Inverse normalization and coordinates for the genuine complex tube. -/

namespace UnitDistance.Witness

noncomputable def studentRealPlaneToComplex (x : StudentRealPlane) : ℂ :=
  (x 0:ℂ)+Complex.I*(x 1:ℂ)

theorem complexToStudentRealPlane_smul (c : ℝ) (z : ℂ) :
    complexToStudentRealPlane (c • z) = c • complexToStudentRealPlane z := by
  ext i
  fin_cases i <;> simp [complexToStudentRealPlane]

theorem complexToStudentRealPlane_inverse (x : StudentRealPlane) :
    complexToStudentRealPlane (studentRealPlaneToComplex x) = x := by
  ext i
  fin_cases i <;> simp [complexToStudentRealPlane, studentRealPlaneToComplex]

/-- Inverse of the manuscript's real normalization. -/
noncomputable def denormalizedStudentPair (x : StudentRealPlane × StudentRealPlane) : ℂ × ℂ :=
  ((Real.sqrt a)⁻¹ • studentRealPlaneToComplex x.1,
   (Real.sqrt a)⁻¹ • studentRealPlaneToComplex x.2)

theorem normalizedStudentPair_denormalized (x : StudentRealPlane × StudentRealPlane) :
    normalizedStudentPair (denormalizedStudentPair x) = x := by
  have ha : Real.sqrt a ≠ 0 := Real.sqrt_ne_zero'.mpr witness_basic.2.1
  simp only [normalizedStudentPair, denormalizedStudentPair, complexToStudentRealPlane_smul,
    complexToStudentRealPlane_inverse, smul_smul, mul_inv_cancel₀ ha, one_smul, Prod.mk.eta]

noncomputable def studentComplexPlaneReal (z : StudentComplexPlane) : StudentRealPlane :=
  WithLp.toLp 2 (fun i => (z i).re)

noncomputable def studentComplexPlaneImag (z : StudentComplexPlane) : StudentRealPlane :=
  WithLp.toLp 2 (fun i => (z i).im)

theorem complexShift_real_imag (z : StudentComplexPlane) :
    BernsteinTube.complexShift (studentComplexPlaneReal z) (studentComplexPlaneImag z) = z := by
  funext i
  apply Complex.ext <;> simp [BernsteinTube.complexShift_re,
    BernsteinTube.complexShift_im, studentComplexPlaneReal, studentComplexPlaneImag]

/-- The actual geometric tube, defined solely by Euclidean norms of the two
imaginary coordinate vectors. -/
def studentPairTube : Set (StudentComplexPlane × StudentComplexPlane) :=
  {z | ‖studentComplexPlaneImag z.1‖ ≤ 1/1000 ∧ ‖studentComplexPlaneImag z.2‖ ≤ 1/1000}

/-- Holomorphy on the independently specified geometric tube. -/
theorem complexPairWeight_differentiableAt_of_mem_tube
    (z : StudentComplexPlane × StudentComplexPlane) (hz : z ∈ studentPairTube) :
    DifferentiableAt ℂ complexPairWeight z := by
  have h := complexPairWeight_differentiableAt
    (studentComplexPlaneReal z.1, studentComplexPlaneReal z.2)
    (studentComplexPlaneImag z.1, studentComplexPlaneImag z.2) hz.1 hz.2
  simpa only [pairComplexShift, complexShift_real_imag, Prod.mk.eta] using h

/-- The published pointwise majorant in arbitrary normalized real coordinates,
ready for one-coordinate contour shifts. -/
theorem complexPairWeight_normalized_norm_le
    (x y : StudentRealPlane × StudentRealPlane)
    (hy1 : ‖y.1‖ ≤ 1/1000) (hy2 : ‖y.2‖ ≤ 1/1000) :
    ‖complexPairWeight (pairComplexShift x y)‖ ≤ fourierTubeConstant *
      ((1+‖x.1‖^2)^(-s*p) * (1+‖x.2‖^2)^(-s*p) * 14^p) := by
  have hbound := complexPairWeight_norm_le (denormalizedStudentPair x) y hy1 hy2
  rw [normalizedStudentPair_denormalized] at hbound
  have hx1 := normalizedStudentPair_fst_norm_sq (denormalizedStudentPair x)
  have hx2 := normalizedStudentPair_snd_norm_sq (denormalizedStudentPair x)
  rw [normalizedStudentPair_denormalized] at hx1 hx2
  have hprofile := pairProfile_rpow_le (denormalizedStudentPair x) witness_basic.2.2.1.le
  simp only [studentWeight, ← hx1, ← hx2, ← neg_mul] at hprofile
  have hq : (0:ℝ) ≤ (fourierTubeLoss:ℝ) := by exact_mod_cast fourierTubeLoss_nonneg
  have hK : 0 ≤ fourierTubeConstant := by unfold fourierTubeConstant; positivity
  exact hbound.trans (mul_le_mul_of_nonneg_left hprofile hK)

end UnitDistance.Witness
