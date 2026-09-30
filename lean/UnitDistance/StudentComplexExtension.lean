module

public import UnitDistance.StudentComplexPolynomial
public import UnitDistance.StudentComplexDenominator
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section
set_option backward.privateInPublic true


/-!
# A genuine holomorphic extension of the polynomial Student weight

The extension uses the principal complex powers of independently defined
quadratic denominators and the actual Bernstein polynomial. Its branch
conditions are proved on the prescribed geometric tube.
-/

open scoped BigOperators

namespace UnitDistance.Witness

abbrev StudentRealPlane := EuclideanSpace ℝ (Fin 2)
abbrev StudentComplexPlane := Fin 2 → ℂ

/-- Complexification in normalized coordinates `x = sqrt(a) z`. The exact
published real exponent `p` is retained, including in the polynomial factor. -/
noncomputable def complexPairWeight (z : StudentComplexPlane × StudentComplexPlane) : ℂ :=
  (BernsteinTube.studentDenominator z.1)^((-s*p:ℝ):ℂ) *
  (BernsteinTube.studentDenominator z.2)^((-s*p:ℝ):ℂ) *
  (complexPolynomial (BernsteinTube.studentDenominator z.1)⁻¹
    (BernsteinTube.studentDenominator z.2)⁻¹)^(p:ℂ)

noncomputable def pairComplexShift (x y : StudentRealPlane × StudentRealPlane) :
    StudentComplexPlane × StudentComplexPlane :=
  (BernsteinTube.complexShift x.1 y.1, BernsteinTube.complexShift x.2 y.2)

private theorem normalized_coordinate_bounds (x : StudentRealPlane) :
    0 < (1+‖x‖^2)⁻¹ ∧ (1+‖x‖^2)⁻¹ ≤ 1 := by
  have h : 0 < 1+‖x‖^2 := by positivity
  exact ⟨inv_pos.mpr h, (inv_le_one₀ h).mpr (by nlinarith [sq_nonneg ‖x‖])⟩

private theorem denominator_re_pos (x y : StudentRealPlane) (hy : ‖y‖ ≤ 1/1000) :
    0 < (BernsteinTube.studentDenominator (BernsteinTube.complexShift x y)).re :=
  BernsteinTube.studentDenominator_re_pos x y (by norm_num) (by norm_num) hy

private theorem inverse_displacement_le (x y : StudentRealPlane) (hy : ‖y‖ ≤ 1/1000) :
    ‖(BernsteinTube.studentDenominator (BernsteinTube.complexShift x y))⁻¹ -
      (((1+‖x‖^2)⁻¹:ℝ):ℂ)‖ ≤ (fourierTubeOmega:ℝ) := by
  have h := BernsteinTube.studentDenominator_inv_sub_real_norm_le x y
    (by norm_num : (0:ℝ) ≤ 1/1000) (by norm_num : (1/1000:ℝ)<1) hy
  norm_num [fourierTubeOmega_eq] at h ⊢
  exact h

/-- The noninteger polynomial power is on its holomorphic principal branch
throughout the actual product of imaginary Euclidean balls. -/
theorem complexPolynomial_denominator_re_pos (x y : StudentRealPlane × StudentRealPlane)
    (hy1 : ‖y.1‖ ≤ 1/1000) (hy2 : ‖y.2‖ ≤ 1/1000) :
    0 < (complexPolynomial
      (BernsteinTube.studentDenominator (pairComplexShift x y).1)⁻¹
      (BernsteinTube.studentDenominator (pairComplexShift x y).2)⁻¹).re := by
  obtain ⟨hx10, hx11⟩ := normalized_coordinate_bounds x.1
  obtain ⟨hx20, hx21⟩ := normalized_coordinate_bounds x.2
  have h := complexPolynomial_re_pos hx10.le hx11 hx20.le hx21 _ _
    (inverse_displacement_le x.1 y.1 hy1) (inverse_displacement_le x.2 y.2 hy2)
  simpa only [pairComplexShift, add_sub_cancel] using h

private theorem differentiable_studentDenominator :
    Differentiable ℂ (BernsteinTube.studentDenominator (ι:=Fin 2)) := by
  unfold BernsteinTube.studentDenominator
  fun_prop

private theorem differentiable_complexPolynomial :
    Differentiable ℂ (fun z : ℂ × ℂ => complexPolynomial z.1 z.2) := by
  unfold complexPolynomial BernsteinTube.patch BernsteinTube.basis
  fun_prop

/-- Actual complex differentiability at every point of the closed geometric
tube. No assumption of holomorphy or nonvanishing occurs in the statement. -/
theorem complexPairWeight_differentiableAt (x y : StudentRealPlane × StudentRealPlane)
    (hy1 : ‖y.1‖ ≤ 1/1000) (hy2 : ‖y.2‖ ≤ 1/1000) :
    DifferentiableAt ℂ complexPairWeight (pairComplexShift x y) := by
  have hd1 : DifferentiableAt ℂ (fun z : StudentComplexPlane × StudentComplexPlane =>
      BernsteinTube.studentDenominator z.1) (pairComplexShift x y) :=
    differentiable_studentDenominator.differentiableAt.comp _ differentiableAt_fst
  have hd2 : DifferentiableAt ℂ (fun z : StudentComplexPlane × StudentComplexPlane =>
      BernsteinTube.studentDenominator z.2) (pairComplexShift x y) :=
    differentiable_studentDenominator.differentiableAt.comp _ differentiableAt_snd
  have hre1 := denominator_re_pos x.1 y.1 hy1
  have hre2 := denominator_re_pos x.2 y.2 hy2
  have hne1 : BernsteinTube.studentDenominator (pairComplexShift x y).1 ≠ 0 := by
    intro hz
    simp only [pairComplexShift] at hz
    simp [hz] at hre1
  have hne2 : BernsteinTube.studentDenominator (pairComplexShift x y).2 ≠ 0 := by
    intro hz
    simp only [pairComplexShift] at hz
    simp [hz] at hre2
  have hpoly := differentiable_complexPolynomial.differentiableAt.comp (pairComplexShift x y)
    ((hd1.inv hne1).prodMk (hd2.inv hne2))
  exact ((hd1.cpow_const (Or.inl hre1)).mul (hd2.cpow_const (Or.inl hre2))).mul
    (hpoly.cpow_const (Or.inl (complexPolynomial_denominator_re_pos x y hy1 hy2)))

end UnitDistance.Witness
