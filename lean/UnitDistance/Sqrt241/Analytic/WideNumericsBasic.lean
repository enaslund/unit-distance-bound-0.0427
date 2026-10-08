module

public import UnitDistance.Sqrt241.Analytic.NumericsBasic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Directed enclosures of Euler factors at `σ = 1 + 1/4411`

The abscissa of the version-2 hypothesis.  As in `Analytic.NumericsBasic` (which treats
`1 + 1/300` and supplies the σ-independent lemmas used here): for `q = p^k`,
`q^{-σ} = q^{-1} exp(-k log p/4411)`, the exponential is enclosed by its quartic Taylor
polynomials, `log p` by rational bounds, and `-log(1-y)` by partial sums (lower) and the
Taylor remainder (upper).
-/

noncomputable section
open scoped BigOperators

namespace UnitDistance.Sqrt241.Analytic

open UnitDistance.NumberFieldAnalysis

/-- The abscissa `1 + 1/4411` of the version-2 hypothesis. -/
abbrev sigmaW : ℝ := 1 + 1 / 4411

theorem sigmaW_eq : sigmaW = 1 + (1 / 4411 : ℝ) := rfl

/-- The Euler argument of `p^k` at `σ_W`. -/
theorem rpow_neg_sigmaW_pow (p k : ℕ) (hp : 0 < p) :
    ((p ^ k : ℕ) : ℝ) ^ (-sigmaW) =
      ((p : ℝ) ^ k)⁻¹ * Real.exp (-((k : ℝ) * Real.log p / 4411)) := by
  have hq : (0 : ℝ) < ((p ^ k : ℕ) : ℝ) := by positivity
  rw [show -sigmaW = (-1 : ℝ) + (-(1 / 4411 : ℝ)) by norm_num [sigmaW],
    Real.rpow_add hq, Real.rpow_neg_one, Real.rpow_def_of_pos hq]
  push_cast
  rw [Real.log_pow]
  congr 2
  ring

theorem eulerArgW_lower {p k : ℕ} (hp : 0 < p) {hi Y : ℝ} (hlog : Real.log p ≤ hi)
    (h0 : 0 ≤ (k : ℝ) * hi / 4411) (h1 : (k : ℝ) * hi / 4411 ≤ 1)
    (hY : Y ≤ ((p : ℝ) ^ k)⁻¹ * expNegLower ((k : ℝ) * hi / 4411)) :
    Y ≤ ((p ^ k : ℕ) : ℝ) ^ (-sigmaW) := by
  rw [rpow_neg_sigmaW_pow p k hp]
  have hpk : (0 : ℝ) < ((p : ℝ) ^ k)⁻¹ := by positivity
  have hexp : Real.exp (-((k : ℝ) * hi / 4411)) ≤
      Real.exp (-((k : ℝ) * Real.log p / 4411)) := by
    apply Real.exp_le_exp.mpr
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have := mul_le_mul_of_nonneg_left hlog hk
    linarith
  have hb := (expNeg_bounds h0 h1).1
  calc Y ≤ ((p : ℝ) ^ k)⁻¹ * expNegLower ((k : ℝ) * hi / 4411) := hY
    _ ≤ ((p : ℝ) ^ k)⁻¹ * Real.exp (-((k : ℝ) * Real.log p / 4411)) :=
      mul_le_mul_of_nonneg_left (hb.trans hexp) hpk.le

theorem eulerArgW_upper {p k : ℕ} (hp : 0 < p) {lo Y : ℝ} (hlog : lo ≤ Real.log p)
    (h0 : 0 ≤ (k : ℝ) * lo / 4411) (h1 : (k : ℝ) * lo / 4411 ≤ 1)
    (hY : ((p : ℝ) ^ k)⁻¹ * expNegUpper ((k : ℝ) * lo / 4411) ≤ Y) :
    ((p ^ k : ℕ) : ℝ) ^ (-sigmaW) ≤ Y := by
  rw [rpow_neg_sigmaW_pow p k hp]
  have hpk : (0 : ℝ) < ((p : ℝ) ^ k)⁻¹ := by positivity
  have hexp : Real.exp (-((k : ℝ) * Real.log p / 4411)) ≤
      Real.exp (-((k : ℝ) * lo / 4411)) := by
    apply Real.exp_le_exp.mpr
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have := mul_le_mul_of_nonneg_left hlog hk
    linarith
  have hb := (expNeg_bounds h0 h1).2
  calc ((p : ℝ) ^ k)⁻¹ * Real.exp (-((k : ℝ) * Real.log p / 4411)) ≤
      ((p : ℝ) ^ k)⁻¹ * expNegUpper ((k : ℝ) * lo / 4411) :=
        mul_le_mul_of_nonneg_left (hexp.trans hb) hpk.le
    _ ≤ Y := hY

/-- Certified lower bound of an Euler factor `a(p^k)` at `σ_W`. -/
theorem primeEulerLogW_pow_lower {p k : ℕ} (hp : 1 < p) (hk : 0 < k) {hi Y L : ℝ} (N : ℕ)
    (hlog : Real.log p ≤ hi) (h0 : 0 ≤ (k : ℝ) * hi / 4411) (h1 : (k : ℝ) * hi / 4411 ≤ 1)
    (hY0 : 0 ≤ Y) (hY : Y ≤ ((p : ℝ) ^ k)⁻¹ * expNegLower ((k : ℝ) * hi / 4411))
    (hL : L ≤ ∑ i ∈ Finset.range N, Y ^ (i + 1) / (i + 1)) :
    L ≤ primeEulerLog (p ^ k) sigmaW := by
  have hq : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp
  have hy1 : ((p ^ k : ℕ) : ℝ) ^ (-sigmaW) < 1 := prime_rpow_lt_one hq (by norm_num [sigmaW])
  have hYy := eulerArgW_lower (by omega) hlog h0 h1 hY
  unfold primeEulerLog
  exact hL.trans (negLog_lower hY0 hYy hy1 N)

/-- Certified upper bound of an Euler factor `a(p^k)` at `σ_W`. -/
theorem primeEulerLogW_pow_upper {p k : ℕ} (hp : 1 < p) {lo Y U : ℝ} (N : ℕ)
    (hlog : lo ≤ Real.log p) (h0 : 0 ≤ (k : ℝ) * lo / 4411) (h1 : (k : ℝ) * lo / 4411 ≤ 1)
    (hY1 : Y < 1) (hY : ((p : ℝ) ^ k)⁻¹ * expNegUpper ((k : ℝ) * lo / 4411) ≤ Y)
    (hU : ∑ i ∈ Finset.range N, Y ^ (i + 1) / (i + 1) + Y ^ (N + 1) / (1 - Y) ≤ U) :
    primeEulerLog (p ^ k) sigmaW ≤ U := by
  have hyY := eulerArgW_upper (Nat.zero_lt_of_lt hp) hlog h0 h1 hY
  have hy0 : 0 ≤ ((p ^ k : ℕ) : ℝ) ^ (-sigmaW) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold primeEulerLog
  exact (negLog_upper hy0 hyY hY1 N).trans hU

end UnitDistance.Sqrt241.Analytic
