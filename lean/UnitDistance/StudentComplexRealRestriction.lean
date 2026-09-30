module

public import UnitDistance.StudentComplexExtension

@[expose] public section
set_option backward.privateInPublic true


/-! The complex extension restricts to the exact published real p-th power. -/

open scoped BigOperators

namespace UnitDistance.Witness

noncomputable def complexToStudentRealPlane (z : ℂ) : StudentRealPlane :=
  WithLp.toLp 2 ![z.re, z.im]

theorem complexToStudentRealPlane_norm_sq (z : ℂ) :
    ‖complexToStudentRealPlane z‖^2 = ‖z‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Complex.sq_norm, Complex.normSq_apply]
  norm_num [complexToStudentRealPlane, Fin.sum_univ_succ]
  ring

/-- Exactly the manuscript's normalization in each of the two complex
coordinates, retaining the ordinary complex Euclidean norm. -/
noncomputable def normalizedStudentPair (z : ℂ × ℂ) : StudentRealPlane × StudentRealPlane :=
  (Real.sqrt a • complexToStudentRealPlane z.1,
   Real.sqrt a • complexToStudentRealPlane z.2)

theorem normalizedStudentPair_fst_norm_sq (z : ℂ × ℂ) :
    ‖(normalizedStudentPair z).1‖^2 = a*‖z.1‖^2 := by
  simp only [normalizedStudentPair, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    complexToStudentRealPlane_norm_sq, Real.sq_sqrt witness_basic.2.1.le]

theorem normalizedStudentPair_snd_norm_sq (z : ℂ × ℂ) :
    ‖(normalizedStudentPair z).2‖^2 = a*‖z.2‖^2 := by
  simp only [normalizedStudentPair, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    complexToStudentRealPlane_norm_sq, Real.sq_sqrt witness_basic.2.1.le]

theorem studentDenominator_real (x : StudentRealPlane) :
    BernsteinTube.studentDenominator (BernsteinTube.complexShift x 0) =
      ((1+‖x‖^2:ℝ):ℂ) := by
  apply Complex.ext
  · simp only [BernsteinTube.studentDenominator_re, norm_zero, zero_pow (by norm_num : (2:ℕ)≠0),
      sub_zero, Complex.ofReal_re]
  · simp only [BernsteinTube.studentDenominator_im, inner_zero_right, mul_zero, Complex.ofReal_im]

/-- The literal p-th power of the original profile factors into two Student
weights and the p-th power of the same original polynomial. -/
theorem pairProfile_rpow_identity (z : ℂ × ℂ) :
    pairProfile z ^ p =
      (1+a*‖z.1‖^2)^(-s*p) * (1+a*‖z.2‖^2)^(-s*p) *
      (polynomial (1+a*‖z.1‖^2)⁻¹ (1+a*‖z.2‖^2)⁻¹)^p := by
  have hb (w : ℂ) : 0 ≤ 1+a*‖w‖^2 := by have := witness_basic.2.1; positivity
  obtain ⟨ht0, ht1⟩ := student_coordinate_bounds z.1
  obtain ⟨hu0, hu1⟩ := student_coordinate_bounds z.2
  have hP := (polynomial_bounds ht0.le ht1 hu0.le hu1).1
  rw [pairProfile_student_identity]
  unfold studentWeight
  rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (hb _) _) (Real.rpow_nonneg (hb _) _))
      (by linarith : 0 ≤ polynomial _ _),
    Real.mul_rpow (Real.rpow_nonneg (hb _) _) (Real.rpow_nonneg (hb _) _)]
  simp only [← Real.rpow_mul (hb _)]

/-- The independently defined principal-power extension has exactly the
published p-th-power weight as its real restriction. -/
theorem complexPairWeight_real (z : ℂ × ℂ) :
    complexPairWeight (pairComplexShift (normalizedStudentPair z) 0) =
      ((pairProfile z ^ p : ℝ):ℂ) := by
  have hb (w : ℂ) : 0 ≤ 1+a*‖w‖^2 := by have := witness_basic.2.1; positivity
  obtain ⟨ht0, ht1⟩ := student_coordinate_bounds z.1
  obtain ⟨hu0, hu1⟩ := student_coordinate_bounds z.2
  have hP := (polynomial_bounds ht0.le ht1 hu0.le hu1).1
  simp only [complexPairWeight, pairComplexShift, Prod.fst_zero, Prod.snd_zero,
    studentDenominator_real, normalizedStudentPair_fst_norm_sq,
    normalizedStudentPair_snd_norm_sq, ← Complex.ofReal_inv,
    complexPolynomial_ofReal, ← Complex.ofReal_cpow (hb _),
    ← Complex.ofReal_cpow (by linarith : 0 ≤ polynomial _ _),
    ← Complex.ofReal_mul, pairProfile_rpow_identity]

end UnitDistance.Witness
