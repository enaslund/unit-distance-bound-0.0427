module

public import UnitDistance.DedekindEulerLog
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section
set_option backward.privateInPublic true


/-!
# The elementary part of the unconditional prime budget

These are inequalities for independently defined logarithmic Euler factors
and the Tsfasman--Vlăduţ weight. They do not assert the Basic Inequality for
a number-field family. That arithmetic/analytic assertion remains a separate
input wherever the weight budget is used.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace UnitDistance.NumberFieldAnalysis

/-- The unconditional prime-budget weight, with the sum starting at one. -/
def primeBudgetWeight (q : ℝ) : ℝ :=
  2*Real.log q*∑' m : ℕ, (q^(m+1)+1)⁻¹

theorem hasSum_inv_pow_succ {q : ℝ} (hq : 1 < q) :
    HasSum (fun m : ℕ => (q^(m+1))⁻¹) (q-1)⁻¹ := by
  have hq0 : 0 < q := by linarith
  have hgeom := (hasSum_geometric_of_lt_one (inv_nonneg.mpr hq0.le)
    (inv_lt_one_of_one_lt₀ hq)).mul_left q⁻¹
  have hefunc : (fun m : ℕ => q⁻¹*q⁻¹^m) = fun m => (q^(m+1))⁻¹ := by
    funext m
    simp [pow_succ, mul_comm, inv_pow]
  rw [hefunc] at hgeom
  have he : q⁻¹*(1-q⁻¹)⁻¹ = (q-1)⁻¹ := by field_simp
  rwa [he] at hgeom

theorem summable_primeBudgetWeight_terms {q : ℝ} (hq : 1 < q) :
    Summable (fun m : ℕ => (q^(m+1)+1)⁻¹) := by
  have hq0 : 0 < q := by linarith
  exact (hasSum_inv_pow_succ hq).summable.of_nonneg_of_le
    (fun m => inv_nonneg.mpr (by positivity))
    (fun m => inv_anti₀ (pow_pos hq0 _) (by linarith))

theorem primeBudgetWeight_nonneg {q : ℝ} (hq : 1 < q) : 0 ≤ primeBudgetWeight q := by
  unfold primeBudgetWeight
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hq.le))
    (tsum_nonneg fun m => inv_nonneg.mpr (by positivity))

/-- The difference between the geometric weight and half the unconditional
weight is bounded by the convergent quadratic geometric tail. -/
theorem primeBudgetWeight_debit {q : ℝ} (hq : 1 < q) :
    Real.log q/(q-1) ≤ primeBudgetWeight q/2 + Real.log q/(q^2-1) := by
  have hq0 : 0 < q := by linarith
  have hq2 : 1 < q^2 := by nlinarith
  have ha := hasSum_inv_pow_succ hq
  have hb := (summable_primeBudgetWeight_terms hq).hasSum
  have hc := hasSum_inv_pow_succ hq2
  have hle : ∀ m : ℕ,
      (q^(m+1))⁻¹-(q^(m+1)+1)⁻¹ ≤ ((q^2)^(m+1))⁻¹ := by
    intro m
    have hx : 0 < q^(m+1) := pow_pos hq0 _
    have he : (q^2)^(m+1) = (q^(m+1))^2 := by ring
    rw [he]
    field_simp
    nlinarith [sq_nonneg (q^(m+1)), pow_pos hx 3]
  have hsum := hasSum_le hle (ha.sub hb) hc
  have hmul := mul_le_mul_of_nonneg_left hsum (Real.log_nonneg hq.le)
  unfold primeBudgetWeight
  simp only [div_eq_mul_inv] at *
  nlinarith

/-- Changing the abscissa from one to `1+epsilon` costs at most the
geometric prime weight. This is a real inequality, valid before taking
any asymptotic family limit. -/
theorem primeEulerLog_sub_le {q : ℕ} (hq : 1 < q) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    primeEulerLog q 1-primeEulerLog q (1+epsilon) ≤
      epsilon*Real.log q/((q : ℝ)-1) := by
  have hq1 : (1:ℝ) < q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hu : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  have hv : (q : ℝ)^(-(1+epsilon)) < 1 :=
    prime_rpow_lt_one hq (by linarith)
  have hlog := Real.log_le_sub_one_of_pos
    (div_pos (sub_pos.mpr hv) (sub_pos.mpr hu))
  rw [Real.log_div (sub_pos.mpr hv).ne' (sub_pos.mpr hu).ne'] at hlog
  have he : (q : ℝ)^(-(1+epsilon)) =
      (q : ℝ)⁻¹*Real.exp (-(epsilon*Real.log q)) := by
    rw [show -(1+epsilon) = -(1:ℝ)+(-epsilon) by ring,
      Real.rpow_add hq0, Real.rpow_neg_one, Real.rpow_def_of_pos hq0]
    congr 2
    ring
  have hexp := Real.add_one_le_exp (-(epsilon*Real.log q))
  have hdiff : (1-(q : ℝ)^(-(1+epsilon)))/(1-(q : ℝ)⁻¹)-1 ≤
      epsilon*Real.log q/((q : ℝ)-1) := by
    rw [he]
    apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
    have hid : ((1-(q : ℝ)⁻¹*Real.exp (-(epsilon*Real.log q)))/
        (1-(q : ℝ)⁻¹)-1)*((q : ℝ)-1) =
        1-Real.exp (-(epsilon*Real.log q)) := by
      field_simp [hq0.ne', sub_ne_zero.mpr hq1.ne',
        show -1+(q:ℝ) ≠ 0 by linarith]
      ring
    rw [hid]
    linarith
  unfold primeEulerLog
  rw [Real.rpow_neg_one]
  linarith

/-- The two scalar inequalities combine into the precise per-norm debit
used by the unconditional prime-budget argument. -/
theorem primeEulerLog_le_budget {q : ℕ} (hq : 1 < q) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    primeEulerLog q 1 ≤ primeEulerLog q (1+epsilon) +
      epsilon*(primeBudgetWeight q/2+Real.log q/((q : ℝ)^2-1)) := by
  have h := primeEulerLog_sub_le hq hepsilon
  have hw := mul_le_mul_of_nonneg_left
    (primeBudgetWeight_debit (q := (q:ℝ)) (by exact_mod_cast hq)) hepsilon
  rw [← mul_div_assoc] at hw
  linarith

theorem primeEulerLog_antitone_exponent {q : ℕ} (hq : 1 < q) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) : primeEulerLog q t ≤ primeEulerLog q s := by
  apply neg_le_neg
  apply Real.log_le_log (sub_pos.mpr (prime_rpow_lt_one hq hs))
  have hp := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq.le : (1:ℝ) ≤ q)
    (neg_le_neg hst)
  linarith

theorem continuousAt_primeEulerLog {q : ℕ} (hq : 1 < q) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (primeEulerLog q) s := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hp : ContinuousAt (fun t : ℝ => (q : ℝ)^(-t)) s :=
    (Real.continuousAt_const_rpow hq0.ne').comp continuousAt_id.neg
  exact ((continuousAt_const.sub hp).log (sub_pos.mpr (prime_rpow_lt_one hq hs)).ne').neg

/-- Once the limiting Euler series is summable at one, its right boundary
limit is justified by domination by that same series. -/
theorem tendsto_primeEulerLog_tsum_boundary {ι : Type*} (q : ι → ℕ) (beta : ι → ℝ)
    (hq : ∀ i, 1 < q i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable (fun i => beta i*primeEulerLog (q i) 1)) :
    Tendsto (fun epsilon : ℝ => ∑' i, beta i*primeEulerLog (q i) (1+epsilon))
      (𝓝[>] 0) (𝓝 (∑' i, beta i*primeEulerLog (q i) 1)) := by
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro i
    have hc : ContinuousAt (fun epsilon : ℝ => primeEulerLog (q i) (1+epsilon)) 0 :=
      ContinuousAt.comp' (f := fun epsilon : ℝ => 1+epsilon) (g := primeEulerLog (q i)) (x := 0)
        (by simpa using continuousAt_primeEulerLog (hq i) (by norm_num : (0:ℝ)<1))
        (continuousAt_const.add continuousAt_id)
    simpa using (hc.const_mul (beta i)).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    change 0 < epsilon at hepsilon
    intro i
    have hn : 0 ≤ beta i*primeEulerLog (q i) (1+epsilon) :=
      mul_nonneg (hbeta i) (primeEulerLog_nonneg (hq i) (by linarith))
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left (primeEulerLog_antitone_exponent (hq i)
      (by norm_num : (0:ℝ)<1) (by linarith)) (hbeta i)

/-- Finite-subset form of the budget conclusion. Since all endpoint Euler
terms are nonnegative, uniform finite-subset budgets also prove convergence
of their infinite sum; convergence at one is not an extra assumption. -/
theorem primeBudget_finite_sum_le {ι : Type*} (q : ι → ℕ) (beta : ι → ℝ)
    (hq : ∀ i, 1 < q i) (hbeta : ∀ i, 0 ≤ beta i)
    {epsilon Y B R : ℝ} (hepsilon : 0 ≤ epsilon) (J : Finset ι)
    (hY : ∑ i ∈ J, beta i*primeEulerLog (q i) (1+epsilon) ≤ Y)
    (hB : ∑ i ∈ J, beta i*primeBudgetWeight (q i) ≤ B)
    (hR : ∑ i ∈ J, beta i*(Real.log (q i)/((q i : ℝ)^2-1)) ≤ R) :
    ∑ i ∈ J, beta i*primeEulerLog (q i) 1 ≤ Y+epsilon*(B/2+R) := by
  calc
    _ ≤ ∑ i ∈ J, (beta i*primeEulerLog (q i) (1+epsilon) +
        epsilon*(beta i*primeBudgetWeight (q i)/2+
          beta i*(Real.log (q i)/((q i : ℝ)^2-1)))) := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left (primeEulerLog_le_budget (hq i) hepsilon) (hbeta i)
      convert h using 1
      ring
    _ = (∑ i ∈ J, beta i*primeEulerLog (q i) (1+epsilon)) +
        epsilon*((∑ i ∈ J, beta i*primeBudgetWeight (q i))/2 +
          ∑ i ∈ J, beta i*(Real.log (q i)/((q i : ℝ)^2-1))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ _ := add_le_add hY (mul_le_mul_of_nonneg_left
      (add_le_add (div_le_div_of_nonneg_right hB (by norm_num)) hR) hepsilon)

/-- The unconditional weight budget implies the infinite Euler ceiling,
with the claimed `epsilon*(B/2+R)` debit. The mathematical input is the
weight budget itself, here stated on every finite subset. -/
theorem primeBudget_tsum_le {ι : Type*} (q : ι → ℕ) (beta : ι → ℝ)
    (hq : ∀ i, 1 < q i) (hbeta : ∀ i, 0 ≤ beta i)
    {epsilon Y B R : ℝ} (hepsilon : 0 ≤ epsilon)
    (hY : ∀ J : Finset ι, ∑ i ∈ J, beta i*primeEulerLog (q i) (1+epsilon) ≤ Y)
    (hB : ∀ J : Finset ι, ∑ i ∈ J, beta i*primeBudgetWeight (q i) ≤ B)
    (hR : ∀ J : Finset ι, ∑ i ∈ J, beta i*(Real.log (q i)/((q i : ℝ)^2-1)) ≤ R) :
    Summable (fun i => beta i*primeEulerLog (q i) 1) ∧
      (∑' i, beta i*primeEulerLog (q i) 1) ≤ Y+epsilon*(B/2+R) := by
  have hnonneg : ∀ i, 0 ≤ beta i*primeEulerLog (q i) 1 := fun i =>
    mul_nonneg (hbeta i) (primeEulerLog_nonneg (hq i) (by norm_num))
  have hbound := fun J => primeBudget_finite_sum_le q beta hq hbeta hepsilon J
    (hY J) (hB J) (hR J)
  exact ⟨summable_of_sum_le hnonneg hbound, Real.tsum_le_of_sum_le hnonneg hbound⟩

end UnitDistance.NumberFieldAnalysis
