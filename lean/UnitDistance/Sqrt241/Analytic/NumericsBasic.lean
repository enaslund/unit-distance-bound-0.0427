module

public import UnitDistance.DedekindEulerLog
public import UnitDistance.PrimeDebit
public import UnitDistance.LogBounds

@[expose] public section
set_option backward.privateInPublic true


/-!
# Directed enclosures of Euler factors at `σ = 1 + 1/300`

Generic lemmas behind the generated certificates of `Analytic.Numerics`.
For `q = p^k`, `q^{-σ} = q^{-1} exp(-k log p/300)`; the exponential is
enclosed by its degree-three Taylor polynomial with Mathlib's remainder
`Real.exp_bound`, the logarithm `log p` by rational bounds, and
`-log(1-y)` by partial sums of its series (lower) and the Taylor remainder
(upper).  The prime-debit weight `log q/(q²-1)` is enclosed directly.
-/

noncomputable section
open scoped BigOperators

namespace UnitDistance.Sqrt241.Analytic

open UnitDistance.NumberFieldAnalysis

/-- The abscissa `1 + 1/300` of the fixed-base hypothesis. -/
abbrev sigma : ℝ := 1 + 1 / 300

theorem sigma_eq : sigma = 1 + (1 / 300 : ℝ) := rfl

/-- Lower quartic enclosure of `exp(-t)`. -/
def expNegLower (t : ℝ) : ℝ := 1 - t + t ^ 2 / 2 - t ^ 3 / 6 - 5 * t ^ 4 / 96

/-- Upper quartic enclosure of `exp(-t)`. -/
def expNegUpper (t : ℝ) : ℝ := 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + 5 * t ^ 4 / 96

theorem expNeg_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    expNegLower t ≤ Real.exp (-t) ∧ Real.exp (-t) ≤ expNegUpper t := by
  have hx : |(-t)| ≤ 1 := by rw [abs_neg, abs_of_nonneg h0]; exact h1
  have h := Real.exp_bound hx (n := 4) (by norm_num)
  rw [abs_neg, abs_of_nonneg h0] at h
  have h' := abs_sub_le_iff.1 h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.succ_eq_add_one] at h'
  norm_num at h'
  constructor
  · unfold expNegLower
    nlinarith [h'.1, h'.2]
  · unfold expNegUpper
    nlinarith [h'.1, h'.2]

/-- The Euler argument of `p^k` at `σ`. -/
theorem rpow_neg_sigma_pow (p k : ℕ) (hp : 0 < p) :
    ((p ^ k : ℕ) : ℝ) ^ (-sigma) =
      ((p : ℝ) ^ k)⁻¹ * Real.exp (-((k : ℝ) * Real.log p / 300)) := by
  have hq : (0 : ℝ) < ((p ^ k : ℕ) : ℝ) := by positivity
  rw [show -sigma = (-1 : ℝ) + (-(1 / 300 : ℝ)) by norm_num [sigma],
    Real.rpow_add hq, Real.rpow_neg_one, Real.rpow_def_of_pos hq]
  push_cast
  rw [Real.log_pow]
  congr 2
  ring

theorem eulerArg_lower {p k : ℕ} (hp : 0 < p) {hi Y : ℝ} (hlog : Real.log p ≤ hi)
    (h0 : 0 ≤ (k : ℝ) * hi / 300) (h1 : (k : ℝ) * hi / 300 ≤ 1)
    (hY : Y ≤ ((p : ℝ) ^ k)⁻¹ * expNegLower ((k : ℝ) * hi / 300)) :
    Y ≤ ((p ^ k : ℕ) : ℝ) ^ (-sigma) := by
  rw [rpow_neg_sigma_pow p k hp]
  have hpk : (0 : ℝ) < ((p : ℝ) ^ k)⁻¹ := by positivity
  have hexp : Real.exp (-((k : ℝ) * hi / 300)) ≤
      Real.exp (-((k : ℝ) * Real.log p / 300)) := by
    apply Real.exp_le_exp.mpr
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have := mul_le_mul_of_nonneg_left hlog hk
    linarith
  have hb := (expNeg_bounds h0 h1).1
  calc Y ≤ ((p : ℝ) ^ k)⁻¹ * expNegLower ((k : ℝ) * hi / 300) := hY
    _ ≤ ((p : ℝ) ^ k)⁻¹ * Real.exp (-((k : ℝ) * Real.log p / 300)) :=
      mul_le_mul_of_nonneg_left (hb.trans hexp) hpk.le

theorem eulerArg_upper {p k : ℕ} (hp : 0 < p) {lo Y : ℝ} (hlog : lo ≤ Real.log p)
    (h0 : 0 ≤ (k : ℝ) * lo / 300) (h1 : (k : ℝ) * lo / 300 ≤ 1)
    (hY : ((p : ℝ) ^ k)⁻¹ * expNegUpper ((k : ℝ) * lo / 300) ≤ Y) :
    ((p ^ k : ℕ) : ℝ) ^ (-sigma) ≤ Y := by
  rw [rpow_neg_sigma_pow p k hp]
  have hpk : (0 : ℝ) < ((p : ℝ) ^ k)⁻¹ := by positivity
  have hexp : Real.exp (-((k : ℝ) * Real.log p / 300)) ≤
      Real.exp (-((k : ℝ) * lo / 300)) := by
    apply Real.exp_le_exp.mpr
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have := mul_le_mul_of_nonneg_left hlog hk
    linarith
  have hb := (expNeg_bounds h0 h1).2
  calc ((p : ℝ) ^ k)⁻¹ * Real.exp (-((k : ℝ) * Real.log p / 300)) ≤
      ((p : ℝ) ^ k)⁻¹ * expNegUpper ((k : ℝ) * lo / 300) :=
        mul_le_mul_of_nonneg_left (hexp.trans hb) hpk.le
    _ ≤ Y := hY

/-- Partial sums of the series of `-log(1-y)` are lower bounds. -/
theorem negLog_lower {y Y : ℝ} (hY0 : 0 ≤ Y) (hYy : Y ≤ y) (hy1 : y < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, Y ^ (i + 1) / (i + 1) ≤ -Real.log (1 - y) := by
  have hY1 : Y < 1 := lt_of_le_of_lt hYy hy1
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := Y) (by rw [abs_of_nonneg hY0]; exact hY1)
  have hpart : ∑ i ∈ Finset.range N, Y ^ (i + 1) / (i + 1) ≤ -Real.log (1 - Y) := by
    apply sum_le_hasSum (Finset.range N) _ hs
    intro i _
    positivity
  have hmono : -Real.log (1 - Y) ≤ -Real.log (1 - y) := by
    apply neg_le_neg
    exact Real.log_le_log (by linarith) (by linarith)
  linarith

/-- Taylor upper bound for `-log(1-y)`. -/
theorem negLog_upper {y Y : ℝ} (hy0 : 0 ≤ y) (hyY : y ≤ Y) (hY1 : Y < 1) (N : ℕ) :
    -Real.log (1 - y) ≤
      ∑ i ∈ Finset.range N, Y ^ (i + 1) / (i + 1) + Y ^ (N + 1) / (1 - Y) := by
  have hY0 : 0 ≤ Y := hy0.trans hyY
  have hlog : -Real.log (1 - y) ≤ -Real.log (1 - Y) := by
    apply neg_le_neg
    exact Real.log_le_log (by linarith) (by linarith)
  have ht := Real.abs_log_sub_add_sum_range_le (x := Y) (by rw [abs_of_nonneg hY0]; exact hY1) N
  have hrem : -((|Y| ^ (N + 1)) / (1 - |Y|)) ≤
      (∑ i ∈ Finset.range N, Y ^ (i + 1) / (i + 1)) + Real.log (1 - Y) :=
    neg_le_of_abs_le ht
  rw [abs_of_nonneg hY0] at hrem
  linarith

/-- Certified lower bound of an Euler factor `a(p^k)` at `σ`. -/
theorem primeEulerLog_pow_lower {p k : ℕ} (hp : 1 < p) (hk : 0 < k) {hi Y L : ℝ} (N : ℕ)
    (hlog : Real.log p ≤ hi) (h0 : 0 ≤ (k : ℝ) * hi / 300) (h1 : (k : ℝ) * hi / 300 ≤ 1)
    (hY0 : 0 ≤ Y) (hY : Y ≤ ((p : ℝ) ^ k)⁻¹ * expNegLower ((k : ℝ) * hi / 300))
    (hL : L ≤ ∑ i ∈ Finset.range N, Y ^ (i + 1) / (i + 1)) :
    L ≤ primeEulerLog (p ^ k) sigma := by
  have hq : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp
  have hy1 : ((p ^ k : ℕ) : ℝ) ^ (-sigma) < 1 := prime_rpow_lt_one hq (by norm_num [sigma])
  have hYy := eulerArg_lower (by omega) hlog h0 h1 hY
  unfold primeEulerLog
  exact hL.trans (negLog_lower hY0 hYy hy1 N)

/-- Certified upper bound of an Euler factor `a(p^k)` at `σ`. -/
theorem primeEulerLog_pow_upper {p k : ℕ} (hp : 1 < p) {lo Y U : ℝ} (N : ℕ)
    (hlog : lo ≤ Real.log p) (h0 : 0 ≤ (k : ℝ) * lo / 300) (h1 : (k : ℝ) * lo / 300 ≤ 1)
    (hY1 : Y < 1) (hY : ((p : ℝ) ^ k)⁻¹ * expNegUpper ((k : ℝ) * lo / 300) ≤ Y)
    (hU : ∑ i ∈ Finset.range N, Y ^ (i + 1) / (i + 1) + Y ^ (N + 1) / (1 - Y) ≤ U) :
    primeEulerLog (p ^ k) sigma ≤ U := by
  have hyY := eulerArg_upper (Nat.zero_lt_of_lt hp) hlog h0 h1 hY
  have hy0 : 0 ≤ ((p ^ k : ℕ) : ℝ) ^ (-sigma) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold primeEulerLog
  exact (negLog_upper hy0 hyY hY1 N).trans hU

theorem primeDebitWeight_pow_eq (p k : ℕ) :
    primeDebitWeight (((p ^ k : ℕ) : ℝ)) = (k : ℝ) * Real.log p / (((p : ℝ) ^ k) ^ 2 - 1) := by
  unfold primeDebitWeight
  push_cast
  rw [Real.log_pow]

/-- Certified lower bound of the debit weight of `p^k`. -/
theorem primeDebitWeight_pow_lower {p k : ℕ} (hp : 1 < p) (hk : 0 < k) {lo L : ℝ}
    (hlog : lo ≤ Real.log p) (hL : L ≤ (k : ℝ) * lo / (((p : ℝ) ^ k) ^ 2 - 1)) :
    L ≤ primeDebitWeight (((p ^ k : ℕ) : ℝ)) := by
  rw [primeDebitWeight_pow_eq p k]
  have hpk : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ (by exact_mod_cast hp) hk.ne'
  have hd : 0 < ((p : ℝ) ^ k) ^ 2 - 1 := by nlinarith
  refine hL.trans (div_le_div_of_nonneg_right ?_ hd.le)
  exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)

/-- Certified upper bound of the debit weight of `p^k`. -/
theorem primeDebitWeight_pow_upper {p k : ℕ} (hp : 1 < p) (hk : 0 < k) {hi U : ℝ}
    (hlog : Real.log p ≤ hi) (hU : (k : ℝ) * hi / (((p : ℝ) ^ k) ^ 2 - 1) ≤ U) :
    primeDebitWeight (((p ^ k : ℕ) : ℝ)) ≤ U := by
  rw [primeDebitWeight_pow_eq p k]
  have hpk : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ (by exact_mod_cast hp) hk.ne'
  have hd : 0 < ((p : ℝ) ^ k) ^ 2 - 1 := by nlinarith
  refine le_trans (div_le_div_of_nonneg_right ?_ hd.le) hU
  exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)

/-- Logarithm of `p = 2^m r` from an enclosure of `log r`. -/
theorem log_bounds_mul_two_pow (p m : ℕ) (r : ℝ) (hr : 0 < r) (hp : (p : ℝ) = 2 ^ m * r)
    {lo2 hi2 lor hir : ℝ} (h2 : lo2 ≤ Real.log 2 ∧ Real.log 2 ≤ hi2)
    (hlr : lor ≤ Real.log r ∧ Real.log r ≤ hir) :
    (m : ℝ) * lo2 + lor ≤ Real.log p ∧ Real.log p ≤ (m : ℝ) * hi2 + hir := by
  rw [hp, Real.log_mul (by positivity) hr.ne', Real.log_pow]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  constructor <;> nlinarith [h2.1, h2.2, hlr.1, hlr.2]

/-- Logarithm of `p = 2^m / r` from an enclosure of `log r`. -/
theorem log_bounds_div_two_pow (p m : ℕ) (r : ℝ) (hr : 0 < r) (hp : (p : ℝ) = 2 ^ m / r)
    {lo2 hi2 lor hir : ℝ} (h2 : lo2 ≤ Real.log 2 ∧ Real.log 2 ≤ hi2)
    (hlr : lor ≤ Real.log r ∧ Real.log r ≤ hir) :
    (m : ℝ) * lo2 - hir ≤ Real.log p ∧ Real.log p ≤ (m : ℝ) * hi2 - lor := by
  rw [hp, Real.log_div (by positivity) hr.ne', Real.log_pow]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  constructor <;> nlinarith [h2.1, h2.2, hlr.1, hlr.2]

theorem log_two_bounds :
    (69314718055994530941 : ℝ) / 10 ^ 20 ≤ Real.log 2 ∧
      Real.log 2 ≤ (69314718055994530942 : ℝ) / 10 ^ 20 := by
  simpa only [div_one] using UnitDistance.log_two_precise

end UnitDistance.Sqrt241.Analytic
