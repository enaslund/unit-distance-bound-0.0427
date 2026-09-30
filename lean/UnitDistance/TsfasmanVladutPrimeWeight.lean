module

public import UnitDistance.TsfasmanVladutKernel
public import UnitDistance.PrimeBudget

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual prime weight of the Tsfasman–Vlăduţ kernel

This module identifies the kernel's prime-power contribution and justifies
the limit as the positive damping parameter tends to zero. It contains no
number-field explicit-formula or asymptotic prime-budget assumption.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace UnitDistance.NumberFieldAnalysis

/-- Positive damping of the unconditional prime-budget weight. -/
def tvPrimeWeight (e q : ℝ) : ℝ :=
  2*Real.log q * ∑' m : ℕ,
    Real.exp (-e*((m+1 : ℕ):ℝ)*Real.log q)/(q^(m+1)+1)

theorem tvPrimeWeight_term_nonneg (e : ℝ) {q : ℝ} (hq : 1 < q) (m : ℕ) :
    0 ≤ Real.exp (-e*((m+1 : ℕ):ℝ)*Real.log q)/(q^(m+1)+1) := by
  positivity

theorem tvPrimeWeight_term_le {e q : ℝ} (he : 0 ≤ e) (hq : 1 < q) (m : ℕ) :
    Real.exp (-e*((m+1 : ℕ):ℝ)*Real.log q)/(q^(m+1)+1) ≤ (q^(m+1)+1)⁻¹ := by
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq.le
  have hexp : Real.exp (-e*((m+1 : ℕ):ℝ)*Real.log q) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg he (Nat.cast_nonneg (m+1)), hlog])
  simpa only [one_div] using div_le_div_of_nonneg_right hexp (by positivity : 0 ≤ q^(m+1)+1)

theorem summable_tvPrimeWeight_terms {e q : ℝ} (he : 0 ≤ e) (hq : 1 < q) :
    Summable (fun m : ℕ => Real.exp (-e*((m+1 : ℕ):ℝ)*Real.log q)/(q^(m+1)+1)) :=
  (summable_primeBudgetWeight_terms hq).of_nonneg_of_le
    (tvPrimeWeight_term_nonneg e hq) (tvPrimeWeight_term_le he hq)

theorem tvPrimeWeight_nonneg (e : ℝ) {q : ℝ} (hq : 1 < q) :
    0 ≤ tvPrimeWeight e q := by
  exact mul_nonneg (by positivity [Real.log_nonneg hq.le])
    (tsum_nonneg (tvPrimeWeight_term_nonneg e hq))

theorem tvPrimeWeight_le_primeBudgetWeight {e q : ℝ} (he : 0 ≤ e) (hq : 1 < q) :
    tvPrimeWeight e q ≤ primeBudgetWeight q := by
  apply mul_le_mul_of_nonneg_left _ (by positivity [Real.log_nonneg hq.le])
  exact Summable.tsum_le_tsum (tvPrimeWeight_term_le he hq)
    (summable_tvPrimeWeight_terms he hq) (summable_primeBudgetWeight_terms hq)

@[simp] theorem tvPrimeWeight_zero (q : ℝ) : tvPrimeWeight 0 q = primeBudgetWeight q := by
  simp only [tvPrimeWeight, primeBudgetWeight, neg_zero, zero_mul, Real.exp_zero, one_div]

/-- The limit of the actual damped prime weight is the full (untruncated)
unconditional prime-budget series. -/
theorem tendsto_tvPrimeWeight_zero {q : ℝ} (hq : 1 < q) :
    Tendsto (fun e : ℝ => tvPrimeWeight e q) (𝓝[>] 0) (𝓝 (primeBudgetWeight q)) := by
  have ht : Tendsto
      (fun e : ℝ => ∑' m : ℕ, Real.exp (-e*((m+1 : ℕ):ℝ)*Real.log q)/(q^(m+1)+1))
      (𝓝[>] 0) (𝓝 (∑' m : ℕ, (q^(m+1)+1)⁻¹)) := by
    apply tendsto_tsum_of_dominated_convergence (summable_primeBudgetWeight_terms hq)
    · intro m
      have hc : ContinuousAt
          (fun e : ℝ => Real.exp (-e*((m+1 : ℕ):ℝ)*Real.log q)/(q^(m+1)+1)) 0 := by
        fun_prop
      simpa only [neg_zero, zero_mul, Real.exp_zero, one_div] using
        hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with e he
      intro m
      rw [Real.norm_eq_abs, abs_of_nonneg (tvPrimeWeight_term_nonneg e hq m)]
      exact tvPrimeWeight_term_le (show 0 < e from he).le hq m
  exact ht.const_mul (2*Real.log q)

/-- The cosh denominator gives exactly the factor `2 / (exp x + 1)` after
multiplication by the half-power appearing in the prime side. -/
theorem tvKernel_mul_half_exp (e : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (Real.exp (-x/2) : ℂ)*tvKernel e x =
      ((2*Real.exp (-e*x)/(Real.exp x+1) : ℝ) : ℂ) := by
  have hid : Real.exp (-x/2)*(Real.exp x+1) = 2*Real.cosh (x/2) := by
    rw [mul_add, mul_one, ← Real.exp_add, show -x/2+x = x/2 by ring, Real.cosh_eq]
    simp only [neg_div]
    ring
  simp only [tvKernel, abs_of_nonneg hx, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [← mul_div_assoc, div_eq_div_iff (Real.cosh_pos _).ne' (by positivity : Real.exp x+1 ≠ 0)]
  calc
    _ = Real.exp (-e*x)*(Real.exp (-x/2)*(Real.exp x+1)) := by ring
    _ = _ := by rw [hid]; ring

/-- The literal prime-power summand in the Weil formula at the actual kernel. -/
theorem tvKernel_prime_power_term (e : ℝ) {q : ℝ} (hq : 1 < q) (m : ℕ) :
    ((Real.log q*q^(-(((m+1:ℕ):ℝ)/2)) : ℝ) : ℂ) *
      tvKernel e (((m+1:ℕ):ℝ)*Real.log q) =
    ((2*Real.log q*Real.exp (-e*((m+1:ℕ):ℝ)*Real.log q)/(q^(m+1)+1) : ℝ) : ℂ) := by
  have hq0 : 0 < q := by linarith
  have hx : 0 ≤ ((m+1:ℕ):ℝ)*Real.log q := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hq.le)
  have hp : q^(-(((m+1:ℕ):ℝ)/2)) = Real.exp (-(((m+1:ℕ):ℝ)*Real.log q)/2) := by
    rw [Real.rpow_def_of_pos hq0]
    congr 1
    ring
  have hpow : Real.exp (((m+1:ℕ):ℝ)*Real.log q) = q^(m+1) := by
    rw [mul_comm, ← Real.rpow_def_of_pos hq0, Real.rpow_natCast]
  rw [Complex.ofReal_mul, hp, mul_assoc, tvKernel_mul_half_exp e hx, hpow]
  rw [← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [show -e*(((m+1:ℕ):ℝ)*Real.log q) = -e*((m+1:ℕ):ℝ)*Real.log q by ring]
  ring

/-- Summing the literal prime-power kernel contributions gives the exact
real damped weight, including its factor of two. -/
theorem hasSum_tvKernel_prime_power_terms {e q : ℝ} (he : 0 ≤ e) (hq : 1 < q) :
    HasSum (fun m : ℕ =>
      ((Real.log q*q^(-(((m+1:ℕ):ℝ)/2)) : ℝ) : ℂ) *
        tvKernel e (((m+1:ℕ):ℝ)*Real.log q)) (tvPrimeWeight e q : ℂ) := by
  simp_rw [tvKernel_prime_power_term e hq]
  apply Complex.hasSum_ofReal.mpr
  have h := (summable_tvPrimeWeight_terms he hq).hasSum.mul_left (2*Real.log q)
  simpa only [tvPrimeWeight, mul_div_assoc] using h

/-- Damping may be removed after restricting to any finite set of norms. -/
theorem tendsto_finset_tvPrimeWeight_zero {ι : Type*} (q beta : ι → ℝ)
    (hq : ∀ i, 1 < q i) (J : Finset ι) :
    Tendsto (fun e : ℝ => ∑ i ∈ J, beta i*tvPrimeWeight e (q i)) (𝓝[>] 0)
      (𝓝 (∑ i ∈ J, beta i*primeBudgetWeight (q i))) := by
  exact tendsto_finsetSum J (fun i _ => (tendsto_tvPrimeWeight_zero (hq i)).const_mul (beta i))

/-- A limiting damped finite-prime bound gives the undamped finite-prime
bound; no interchange of an infinite prime sum with the limit is used. -/
theorem primeBudget_finite_sum_le_of_tvPrimeWeight {ι : Type*} (q beta : ι → ℝ)
    (hq : ∀ i, 1 < q i) (J : Finset ι) {bound : ℝ → ℝ} {B : ℝ}
    (hlim : Tendsto bound (𝓝[>] 0) (𝓝 B))
    (hbound : ∀ᶠ e : ℝ in 𝓝[>] 0, ∑ i ∈ J, beta i*tvPrimeWeight e (q i) ≤ bound e) :
    ∑ i ∈ J, beta i*primeBudgetWeight (q i) ≤ B :=
  le_of_tendsto_of_tendsto (tendsto_finset_tvPrimeWeight_zero q beta hq J) hlim hbound

/-- Uniform finite-prime inequalities also prove convergence of the full
nonnegative budget series. This is the final monotone step of the basic
inequality, after the finite-field analytic estimates have been supplied. -/
theorem primeBudget_summable_le_of_tvPrimeWeight {ι : Type*} (q beta : ι → ℝ)
    (hq : ∀ i, 1 < q i) (hbeta : ∀ i, 0 ≤ beta i) {bound : ℝ → ℝ} {B : ℝ}
    (hlim : Tendsto bound (𝓝[>] 0) (𝓝 B))
    (hbound : ∀ J : Finset ι, ∀ᶠ e : ℝ in 𝓝[>] 0,
      ∑ i ∈ J, beta i*tvPrimeWeight e (q i) ≤ bound e) :
    Summable (fun i => beta i*primeBudgetWeight (q i)) ∧
      (∑' i, beta i*primeBudgetWeight (q i)) ≤ B := by
  have hn : ∀ i, 0 ≤ beta i*primeBudgetWeight (q i) :=
    fun i => mul_nonneg (hbeta i) (primeBudgetWeight_nonneg (hq i))
  have hb := fun J => primeBudget_finite_sum_le_of_tvPrimeWeight q beta hq J hlim (hbound J)
  exact ⟨summable_of_sum_le hn hb, Real.tsum_le_of_sum_le hn hb⟩

end UnitDistance.NumberFieldAnalysis
