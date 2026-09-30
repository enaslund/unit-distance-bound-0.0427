module

public import UnitDistance.Witness
public import Mathlib.Analysis.Analytic.Binomial

@[expose] public section
set_option backward.privateInPublic true


noncomputable section

open scoped Nat

namespace UnitDistance.Witness

theorem hasSum_generalizedBinomial {p x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => Ring.choose p n * x ^ n) ((1 + x) ^ p) := by
  have h := Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := p)
  have hx' : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Real.dist_eq] using hx
  have hs := h.hasSum_sub hx'
  simpa [binomialSeries, FormalMultilinearSeries.coeff_ofScalars, mul_comm] using hs

theorem generalizedChoose_succ (p : ℝ) (n : ℕ) :
    Ring.choose p (n + 1) = Ring.choose p n * (p - n) / (n + 1) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, descPochhammer_succ_right,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, npow_one, npow_zero]
  have hn : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hs : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem abs_generalizedChoose_succ_le {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    {n : ℕ} (hn : 2 ≤ n) :
    |Ring.choose p (n + 1)| ≤ |Ring.choose p n| := by
  rw [generalizedChoose_succ, abs_div, abs_mul]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpn : p ≤ (n : ℝ) := hp2.trans hnR
  have hden : 0 < (n : ℝ) + 1 := by positivity
  rw [abs_of_nonpos (sub_nonpos.mpr hpn), abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  have hnum : -(p - (n : ℝ)) ≤ (n : ℝ) + 1 := by linarith
  exact mul_le_mul_of_nonneg_left hnum (abs_nonneg _)

theorem abs_generalizedChoose_tail_le {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    |Ring.choose p (N + 1 + k)| ≤ |Ring.choose p (N + 1)| := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        |Ring.choose p (N + 1 + (k + 1))| =
            |Ring.choose p ((N + 1 + k) + 1)| := by congr 2 <;> omega
        _ ≤ |Ring.choose p (N + 1 + k)| :=
          abs_generalizedChoose_succ_le hp1 hp2 (by omega)
        _ ≤ _ := ih

/-- Uniform generalized-binomial truncation error used by the local mass
certificate.  The coefficient at the first omitted term controls the whole
tail because absolute generalized binomial coefficients decrease from index
two onward. -/
theorem generalizedBinomial_truncation_error {p x r : ℝ}
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {N : ℕ} (hN : 2 ≤ N)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hxr : |x| ≤ r) :
    |(1 + x) ^ p -
        ∑ k ∈ Finset.range (N + 1), Ring.choose p k * x ^ k| ≤
      |Ring.choose p (N + 1)| * r ^ (N + 1) / (1 - r) := by
  let f : ℕ → ℝ := fun k => Ring.choose p k * x ^ k
  have hx1 : |x| < 1 := hxr.trans_lt hr1
  have hs : HasSum f ((1 + x) ^ p) := by
    simpa only [f] using hasSum_generalizedBinomial hx1
  have htail : HasSum (fun k => f (N + 1 + k))
      ((1 + x) ^ p - ∑ k ∈ Finset.range (N + 1), f k) := by
    simpa only [Nat.add_comm] using
      ((hasSum_nat_add_iff' (f := f) (N + 1)).mpr hs)
  let C : ℝ := |Ring.choose p (N + 1)| * r ^ (N + 1)
  have hterm (k : ℕ) : ‖f (N + 1 + k)‖ ≤ C * r ^ k := by
    have hcoeff := abs_generalizedChoose_tail_le hp1 hp2 hN k
    have hxpow : |x| ^ (N + 1 + k) ≤ r ^ (N + 1 + k) :=
      pow_le_pow_left₀ (abs_nonneg x) hxr _
    calc
      ‖f (N + 1 + k)‖ =
          |Ring.choose p (N + 1 + k)| * |x| ^ (N + 1 + k) := by
        simp only [f, Real.norm_eq_abs, abs_mul, abs_pow]
      _ ≤ |Ring.choose p (N + 1)| * r ^ (N + 1 + k) :=
        mul_le_mul hcoeff hxpow (pow_nonneg (abs_nonneg x) _) (abs_nonneg _)
      _ = C * r ^ k := by
        simp only [C, pow_add]
        ring
  have herr := norm_sub_le_of_geometric_bound_of_hasSum hr1 hterm htail 0
  simpa only [Finset.range_zero, Finset.sum_empty, zero_sub, norm_neg,
    Real.norm_eq_abs, pow_zero, mul_one, f, C] using herr

theorem pairPower_bounds : 1 ≤ p ∧ p ≤ 2 := by
  norm_num [p, increment]

theorem pairPower_binomial_truncation_error {x r : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hxr : |x| ≤ r) :
    |(1 + x) ^ p -
        ∑ k ∈ Finset.range (N + 1), Ring.choose p k * x ^ k| ≤
      |Ring.choose p (N + 1)| * r ^ (N + 1) / (1 - r) :=
  generalizedBinomial_truncation_error pairPower_bounds.1 pairPower_bounds.2 hN
    hr0 hr1 hxr

end UnitDistance.Witness
