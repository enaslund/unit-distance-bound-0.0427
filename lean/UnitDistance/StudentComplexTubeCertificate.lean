module

public import UnitDistance.StudentComplexBernstein
public import Mathlib.Data.NNRat.Defs

@[expose] public section
set_option backward.privateInPublic true


/-!
# The exact Bernstein tube certificate of the published witness

The finite mixed differences, their maxima and the tube loss are defined
directly from the original rational coefficient array. The strict bound is
verified by kernel rational arithmetic, not by floating-point computation.
-/

open scoped BigOperators

namespace UnitDistance.Witness

/-- Zero extension of the actual finite coefficient array. In all differences
used below, the indexing ranges keep the arguments within the original array. -/
def bernsteinCoefficientNat (i j : ℕ) : ℚ :=
  if hi : i < 4 then if hj : j < 4 then bernsteinCoefficients ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

noncomputable def bernsteinDifferenceAbs (r s i j : ℕ) : ℚ≥0 :=
  ⟨|BernsteinTube.difference bernsteinCoefficientNat r s i j|, abs_nonneg _⟩

noncomputable def bernsteinDifferenceBound (r s : ℕ) : ℚ≥0 :=
  ((Finset.range (4-r)) ×ˢ (Finset.range (4-s))).sup
    (fun ij => bernsteinDifferenceAbs r s ij.1 ij.2)

noncomputable def bernsteinTaylorBound (r s : ℕ) : ℚ≥0 :=
  (Nat.choose 3 r : ℚ≥0)*(Nat.choose 3 s : ℚ≥0)*bernsteinDifferenceBound r s

def fourierTubeWidth : ℚ := 1/1000

def fourierTubeOmega : ℚ :=
  (fourierTubeWidth+fourierTubeWidth^2)/(1-fourierTubeWidth^2)

/-- The manuscript's `q0`; the exact minimum coefficient is one. -/
noncomputable def fourierTubeLoss : ℚ :=
  ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4,
    if r+s=0 then 0 else (bernsteinTaylorBound r s : ℚ)*fourierTubeOmega^(r+s)

theorem fourierTubeOmega_eq : fourierTubeOmega = 1/999 := by
  norm_num [fourierTubeOmega, fourierTubeWidth]

/-- Small rational upper bounds for the independently defined mixed-difference
maxima. They are verified against every actual difference below. -/
def bernsteinDifferenceCeiling : ℕ → ℕ → ℚ≥0
  | 0, 0 => 14
  | 0, 1 | 1, 0 => 4315/1000
  | 0, 2 | 2, 0 => 3555/1000
  | 0, 3 | 3, 0 => 4609/1000
  | 1, 1 => 595/1000
  | 1, 2 | 2, 1 => 1015/1000
  | 1, 3 | 3, 1 => 1384/1000
  | 2, 2 => 1398/1000
  | 2, 3 | 3, 2 => 2320/1000
  | 3, 3 => 4497/1000
  | _, _ => 0

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
theorem bernsteinDifferenceAbs_le_ceiling {r s i j : ℕ}
    (hr : r < 4) (hs : s < 4) (hi : i < 4-r) (hj : j < 4-s) :
    bernsteinDifferenceAbs r s i j ≤ bernsteinDifferenceCeiling r s := by
  change |BernsteinTube.difference bernsteinCoefficientNat r s i j| ≤
    (bernsteinDifferenceCeiling r s : ℚ)
  interval_cases r <;> interval_cases s <;> interval_cases i <;> interval_cases j <;>
    norm_num only [BernsteinTube.difference, Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose] <;>
    norm_num [bernsteinCoefficientNat, bernsteinCoefficients, bernsteinDifferenceCeiling]

theorem bernsteinDifferenceBound_le_ceiling {r s : ℕ} (hr : r < 4) (hs : s < 4) :
    bernsteinDifferenceBound r s ≤ bernsteinDifferenceCeiling r s := by
  apply Finset.sup_le
  intro ij hij
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
  exact bernsteinDifferenceAbs_le_ceiling hr hs
    (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)

/-- The certified perturbation sum is strictly smaller than 0.026. Every
quantity on the left is independently defined from the original coefficients. -/
theorem fourierTubeLoss_lt : fourierTubeLoss < 13/500 := by
  let upper : ℚ := ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4,
    if r+s=0 then 0 else
      (Nat.choose 3 r : ℚ)*(Nat.choose 3 s : ℚ)*
        (bernsteinDifferenceCeiling r s : ℚ)*fourierTubeOmega^(r+s)
  have hle : fourierTubeLoss ≤ upper := by
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro s hs
    split_ifs
    · exact le_rfl
    · apply mul_le_mul_of_nonneg_right _ (by rw [fourierTubeOmega_eq]; positivity)
      change (Nat.choose 3 r : ℚ)*(Nat.choose 3 s : ℚ)*(bernsteinDifferenceBound r s : ℚ) ≤ _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast bernsteinDifferenceBound_le_ceiling (Finset.mem_range.mp hr) (Finset.mem_range.mp hs)
  have hupper : upper < 13/500 := by
    norm_num only [upper, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [bernsteinDifferenceCeiling, fourierTubeOmega_eq, Nat.choose]
  exact hle.trans_lt hupper

end UnitDistance.Witness
