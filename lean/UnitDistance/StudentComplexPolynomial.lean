module

public import UnitDistance.StudentComplexEstimate
public import UnitDistance.StudentComplexTubeCertificate

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual Bernstein polynomial is nonvanishing in its certified complex tube

The complex polynomial is independently defined from the published rational
coefficient array. Its real restriction is the original polynomial. Exact
mixed-difference maxima control its perturbation, and the checked tube loss
places its values strictly in the right half-plane.
-/

open scoped BigOperators

namespace UnitDistance.Witness

noncomputable def complexBernsteinCoefficients (i j : ℕ) : ℂ := bernsteinCoefficientNat i j

noncomputable def complexPolynomial (t u : ℂ) : ℂ :=
  BernsteinTube.patch complexBernsteinCoefficients t u

theorem complexPolynomial_ofReal (t u : ℝ) : complexPolynomial (t:ℂ) (u:ℂ) =
    ((polynomial t u : ℝ) : ℂ) := by
  unfold complexPolynomial BernsteinTube.patch polynomial
  simp_rw [← Fin.sum_univ_eq_sum_range]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [complexBernsteinCoefficients, bernsteinCoefficientNat, i.isLt, j.isLt,
    BernsteinTube.basis, bernstein3]

private theorem difference_complex (r s i j : ℕ) :
    BernsteinTube.difference complexBernsteinCoefficients r s i j =
      ((BernsteinTube.difference bernsteinCoefficientNat r s i j : ℚ) : ℂ) := by
  simp [BernsteinTube.difference, complexBernsteinCoefficients]

theorem norm_complex_difference_le {r s i j : ℕ}
    (hi : i ∈ Finset.range (4-r)) (hj : j ∈ Finset.range (4-s)) :
    ‖BernsteinTube.difference complexBernsteinCoefficients r s i j‖ ≤
      (bernsteinDifferenceBound r s : ℝ) := by
  have hle : bernsteinDifferenceAbs r s i j ≤ bernsteinDifferenceBound r s :=
    Finset.le_sup (s := (Finset.range (4-r)) ×ˢ (Finset.range (4-s)))
      (f := fun ij => bernsteinDifferenceAbs r s ij.1 ij.2) (b := (i,j))
      (Finset.mem_product.mpr ⟨hi, hj⟩)
  have hrat : |BernsteinTube.difference bernsteinCoefficientNat r s i j| ≤
      (bernsteinDifferenceBound r s : ℚ) := hle
  rw [difference_complex, Complex.norm_ratCast]
  exact_mod_cast hrat

theorem fourierTubeLoss_nonneg : 0 ≤ fourierTubeLoss := by
  unfold fourierTubeLoss
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro s hs
  split_ifs
  · exact le_rfl
  · rw [fourierTubeOmega_eq]
    positivity

/-- Literal norm control of the published complex polynomial throughout the
product disks around any point of the real unit square. -/
theorem complexPolynomial_perturbation {t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h k : ℂ) (hh : ‖h‖ ≤ (fourierTubeOmega : ℝ)) (hk : ‖k‖ ≤ (fourierTubeOmega : ℝ)) :
    ‖complexPolynomial ((t:ℂ)+h) ((u:ℂ)+k) - (polynomial t u : ℂ)‖ ≤
      (fourierTubeLoss : ℝ) := by
  have hω : 0 ≤ (fourierTubeOmega : ℝ) := by rw [fourierTubeOmega_eq]; norm_num
  have hbound := BernsteinTube.mixed_difference_perturbation_le complexBernsteinCoefficients
    (fun r s => (bernsteinDifferenceBound r s : ℝ)) hω ht0 ht1 hu0 hu1 h k hh hk
    (fun _ _ _ _ => by positivity) (fun _ _ _ _ _ hi _ hj => norm_complex_difference_le hi hj)
  rw [← complexPolynomial_ofReal]
  convert! hbound using 1
  simp only [fourierTubeLoss, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs
  · simp
  · simp [bernsteinTaylorBound]

/-- The actual complex polynomial stays strictly in the right half-plane,
providing the nonvanishing needed for a holomorphic fractional power. -/
theorem complexPolynomial_re_pos {t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h k : ℂ) (hh : ‖h‖ ≤ (fourierTubeOmega : ℝ)) (hk : ‖k‖ ≤ (fourierTubeOmega : ℝ)) :
    0 < (complexPolynomial ((t:ℂ)+h) ((u:ℂ)+k)).re := by
  have hP := (polynomial_bounds ht0 ht1 hu0 hu1).1
  have hdiff := complexPolynomial_perturbation ht0 ht1 hu0 hu1 h k hh hk
  have hq : (fourierTubeLoss : ℝ) < 13/500 := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr fourierTubeLoss_lt
    norm_num at h ⊢
    exact h
  have hre := (abs_le.mp (Complex.abs_re_le_norm
    (complexPolynomial ((t:ℂ)+h) ((u:ℂ)+k) - (polynomial t u : ℂ)))).1
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  linarith

/-- The same certified tube gives the relative upper bound used before
taking the actual p-th power in the Fourier majorant. -/
theorem complexPolynomial_norm_le {t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h k : ℂ) (hh : ‖h‖ ≤ (fourierTubeOmega : ℝ)) (hk : ‖k‖ ≤ (fourierTubeOmega : ℝ)) :
    ‖complexPolynomial ((t:ℂ)+h) ((u:ℂ)+k)‖ ≤
      (1+(fourierTubeLoss : ℝ))*polynomial t u := by
  have hP := (polynomial_bounds ht0 ht1 hu0 hu1).1
  have hdiff := complexPolynomial_perturbation ht0 ht1 hu0 hu1 h k hh hk
  have hq : (0:ℝ) ≤ (fourierTubeLoss : ℝ) := by exact_mod_cast fourierTubeLoss_nonneg
  have htri : ‖complexPolynomial ((t:ℂ)+h) ((u:ℂ)+k)‖ ≤
      ‖complexPolynomial ((t:ℂ)+h) ((u:ℂ)+k) - (polynomial t u : ℂ)‖ + polynomial t u := by
    simpa only [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < polynomial t u by linarith)] using
      norm_add_le (complexPolynomial ((t:ℂ)+h) ((u:ℂ)+k) - (polynomial t u : ℂ)) (polynomial t u : ℂ)
  nlinarith [mul_le_mul_of_nonneg_left hP hq]

end UnitDistance.Witness
