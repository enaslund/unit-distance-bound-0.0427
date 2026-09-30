module

public import UnitDistance.StudentComplexBernstein

@[expose] public section
set_option backward.privateInPublic true


/-!
# Norm bounds from exact Bernstein mixed differences

The real Bernstein weights are a nonnegative partition of unity. Applying
this to the exact finite Taylor coefficients bounds complex perturbations
by ordinary maxima of mixed coefficient differences.
-/

open scoped BigOperators

namespace UnitDistance.BernsteinTube

@[simp] theorem basis_complex_ofReal (n i : ℕ) (t : ℝ) :
    basis n i (t : ℂ) = ((basis n i t : ℝ) : ℂ) := by
  simp [basis]

theorem norm_basis_complex {n i : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖basis n i (t : ℂ)‖ = basis n i t := by
  rw [basis_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (basis_nonneg ht0 ht1)]

theorem taylorCoefficient_norm_le (B : ℕ → ℕ → ℂ) {r s : ℕ} (hr : r ≤ 3) (hs : s ≤ 3)
    {D t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hD : ∀ i ∈ Finset.range (4-r), ∀ j ∈ Finset.range (4-s),
      ‖difference B r s i j‖ ≤ D) :
    ‖taylorCoefficient B r s (t : ℂ) (u : ℂ)‖ ≤
      (Nat.choose 3 r : ℝ)*(Nat.choose 3 s : ℝ)*D := by
  have hsum : (∑ i ∈ Finset.range (4-r), ∑ j ∈ Finset.range (4-s),
      basis (3-r) i t*basis (3-s) j u) = 1 := by
    rw [show 4-r = (3-r)+1 by omega, show 4-s = (3-s)+1 by omega]
    simp_rw [← Finset.mul_sum, basis_sum, mul_one]
    exact basis_sum _ _
  unfold taylorCoefficient
  rw [norm_mul, norm_mul]
  simp only [Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ i ∈ Finset.range (4-r),
        ‖∑ j ∈ Finset.range (4-s), difference B r s i j*basis (3-r) i (t:ℂ)*basis (3-s) j (u:ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (4-r), ∑ j ∈ Finset.range (4-s),
        ‖difference B r s i j*basis (3-r) i (t:ℂ)*basis (3-s) j (u:ℂ)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (4-r), ∑ j ∈ Finset.range (4-s),
        D*(basis (3-r) i t*basis (3-s) j u) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul, norm_basis_complex ht0 ht1, norm_basis_complex hu0 hu1]
      calc
        _ ≤ D*basis (3-r) i t*basis (3-s) j u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hD i hi j hj)
            (basis_nonneg ht0 ht1)) (basis_nonneg hu0 hu1)
        _ = _ := by ring
    _ = D*(∑ i ∈ Finset.range (4-r), ∑ j ∈ Finset.range (4-s),
        basis (3-r) i t*basis (3-s) j u) := by simp only [Finset.mul_sum]
    _ = D := by rw [hsum, mul_one]

@[simp] theorem taylorCoefficient_zero_zero (B : ℕ → ℕ → ℂ) (t u : ℂ) :
    taylorCoefficient B 0 0 t u = patch B t u := by
  simp [taylorCoefficient, difference, patch]

set_option maxHeartbeats 1000000 in
/-- The constant Taylor term is removed exactly; every remaining index has
strictly positive total degree. -/
theorem patch_sub (B : ℕ → ℕ → ℂ) (t u h k : ℂ) :
    patch B (t+h) (u+k) - patch B t u =
      ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4,
        if r+s=0 then 0 else taylorCoefficient B r s t u*h^r*k^s := by
  rw [patch_add]
  norm_num [Finset.sum_range_succ, taylorCoefficient_zero_zero]
  ring

end UnitDistance.BernsteinTube
