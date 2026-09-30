module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Kernel-checkable logarithm enclosures

The checker uses the proved real logarithm series remainder from Mathlib.
Its certificate premises are exact rational inequalities, discharged with
ordinary kernel-checkable arithmetic. No floating-point evaluator is trusted.
-/

open scoped BigOperators

namespace UnitDistance

theorem log_enclosure (q : ℝ) (n : ℕ) (hq : 1 ≤ q) (lo hi : ℝ)
    (hl : lo ≤ 2 * ∑ i ∈ Finset.range n,
      ((q-1)/(q+1))^(2*i+1)/(2*i+1))
    (hu : 2 * ((∑ i ∈ Finset.range n,
      ((q-1)/(q+1))^(2*i+1)/(2*i+1)) +
      ((q-1)/(q+1))^(2*n+1)/(1-((q-1)/(q+1))^2)) ≤ hi) :
    lo ≤ Real.log q ∧ Real.log q ≤ hi := by
  have hd : 0 < q+1 := by linarith
  have hx0 : 0 ≤ (q-1)/(q+1) := div_nonneg (by linarith) hd.le
  have hx1 : (q-1)/(q+1) < 1 := (div_lt_one hd).mpr (by linarith)
  have heq : (1+(q-1)/(q+1))/(1-(q-1)/(q+1)) = q := by
    field_simp
    ring
  have hl' := Real.sum_range_le_log_div hx0 hx1 n
  have hu' := Real.log_div_le_sum_range_add hx0 hx1 n
  rw [heq] at hl' hu'
  constructor <;> linarith

theorem log_two_precise :
    (69314718055994530941 : ℝ) / 10^20 ≤ Real.log ((2 : ℝ) / 1) ∧
      Real.log ((2 : ℝ) / 1) ≤ (69314718055994530942 : ℝ) / 10^20 := by
  apply log_enclosure ((2 : ℝ) / 1) 25 (by norm_num)
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_discriminant_reduced :
    (60589163313814162879 : ℝ) / 10^20 ≤ Real.log ((15015 : ℝ) / 8192) ∧
      Real.log ((15015 : ℝ) / 8192) ≤ (60589163313814162880 : ℝ) / 10^20 := by
  apply log_enclosure ((15015 : ℝ) / 8192) 25 (by norm_num)
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_pi_lower_half :
    (45158270528945486472 : ℝ) / 10^20 ≤ Real.log ((157079632679489661923 : ℝ) / 100000000000000000000) ∧
      Real.log ((157079632679489661923 : ℝ) / 100000000000000000000) ≤ (45158270528945486473 : ℝ) / 10^20 := by
  apply log_enclosure ((157079632679489661923 : ℝ) / 100000000000000000000) 25 (by norm_num)
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_pi_upper_half :
    (45158270528945486472 : ℝ) / 10^20 ≤ Real.log ((314159265358979323847 : ℝ) / 200000000000000000000) ∧
      Real.log ((314159265358979323847 : ℝ) / 200000000000000000000) ≤ (45158270528945486473 : ℝ) / 10^20 := by
  apply log_enclosure ((314159265358979323847 : ℝ) / 200000000000000000000) 25 (by norm_num)
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_increment_inverse_reduced :
    (40170817423045873750 : ℝ) / 10^20 ≤ Real.log ((125000 : ℝ) / 83647) ∧
      Real.log ((125000 : ℝ) / 83647) ≤ (40170817423045873751 : ℝ) / 10^20 := by
  apply log_enclosure ((125000 : ℝ) / 83647) 25 (by norm_num)
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

theorem log_one_add_increment :
    (4097254318723584820 : ℝ) / 10^20 ≤ Real.log ((2083647 : ℝ) / 2000000) ∧
      Real.log ((2083647 : ℝ) / 2000000) ≤ (4097254318723584821 : ℝ) / 10^20 := by
  apply log_enclosure ((2083647 : ℝ) / 2000000) 10 (by norm_num)
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

end UnitDistance
