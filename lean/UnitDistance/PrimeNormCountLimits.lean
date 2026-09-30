module

public import UnitDistance.PrimeNormCounts
public import UnitDistance.PrimeBudget
public import Mathlib.Analysis.PSeries

@[expose] public section
set_option backward.privateInPublic true


/-!
# Fixed-abscissa limits of actual number-field Euler products

For each real `s > 1`, the summable majorant `2*q^(-s)` dominates every
normalized prime-norm Euler summand, independently of the number field.
Consequently coordinatewise convergence of the actual normalized prime
counts implies convergence of the actual normalized zeta logarithm. The
diagonal extraction theorem then provides the same subsequence for every
real abscissa above one.
-/

noncomputable section
open NumberField Filter Topology
open scoped BigOperators

namespace UnitDistance.NumberFieldAnalysis

/-- A uniform elementary Euler majorant on the whole half-line `s ≥ 1`. -/
theorem primeEulerLog_le_two_rpow {q : ℕ} (hq : 1 < q) {s : ℝ} (hs : 1 ≤ s) :
    primeEulerLog q s ≤ 2*(q : ℝ)^(-s) := by
  have hq1 : (1:ℝ) < q := by exact_mod_cast hq
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hp : (q : ℝ)^(-s) ≤ (1/2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hq1.le (neg_le_neg hs)
    rw [Real.rpow_neg_one] at h
    exact h.trans (by simpa using inv_anti₀ (by norm_num : (0:ℝ)<2) hq2)
  have hp0 := Real.rpow_nonneg (Nat.cast_nonneg q) (-s)
  have hden : 0 < 1-(q : ℝ)^(-s) := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hden
  have hdiv : (1-(q : ℝ)^(-s))⁻¹-1 ≤ 2*(q : ℝ)^(-s) := by
    rw [sub_le_iff_le_add]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  unfold primeEulerLog
  linarith

/-- The majorant is summable over *all* possible integer norms. Restriction
to prime powers is unnecessary for the dominated-convergence argument. -/
theorem summable_primeEulerLog_majorant {s : ℝ} (hs : 1 < s) :
    Summable (fun q : ℕ => 2*((q+2 : ℕ) : ℝ)^(-s)) := by
  have h : Summable (fun q : ℕ => (q : ℝ)^(-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact ((summable_nat_add_iff 2).mpr h).mul_left 2

theorem summable_primeEulerLog_all_norms {s : ℝ} (hs : 1 < s) :
    Summable (fun q : ℕ => primeEulerLog (q+2) s) := by
  apply (summable_primeEulerLog_majorant hs).of_nonneg_of_le
  · intro q
    exact primeEulerLog_nonneg (by omega) (by linarith)
  · intro q
    exact primeEulerLog_le_two_rpow (by omega) hs.le

variable (Ks : ℕ → Type*) [∀ n, Field (Ks n)] [∀ n, NumberField (Ks n)]

/-- Coordinatewise prime-count convergence gives the actual normalized Euler
limit at every fixed real abscissa above one. No asymptotic class-number
formula, Galois assumption, or root-discriminant bound is used. -/
theorem normalized_dedekindZeta_tendsto_of_primeNormCounts (beta : ℕ → ℝ)
    (hcounts : ∀ q, Tendsto (fun n => normalizedPrimeNormCount (Ks n) (q+2))
      atTop (𝓝 (beta q))) {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n => Real.log (dedekindZeta (Ks n) s).re /
      (Module.finrank ℚ (Ks n) : ℝ)) atTop
      (𝓝 (∑' q, beta q*primeEulerLog (q+2) s)) := by
  have hlim := tendsto_tsum_of_dominated_convergence
    (summable_primeEulerLog_all_norms hs)
    (fun q => (hcounts q).mul_const (primeEulerLog (q+2) s))
    (Filter.Eventually.of_forall fun n => ?_)
  · apply hlim.congr
    intro n
    exact (normalizedPrimeNormCount_euler_hasSum (Ks n) hs).tsum_eq
  · intro q
    have hc := normalizedPrimeNormCount_mem (Ks n) (q := q+2) (by omega)
    have ha := primeEulerLog_nonneg (q := q+2) (by omega) (by linarith : 0<s)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.1 ha)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc.2 ha

/-- Every sequence of actual number fields has a single subsequence for which
all normalized prime counts and all real normalized Euler logarithms above
one converge. The limiting Euler functions are the actual prime-count sums. -/
theorem exists_subsequence_normalized_dedekindZeta_limits :
    ∃ (beta : ℕ → ℝ) (phi : ℕ → ℕ), StrictMono phi ∧
      (∀ q, beta q ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ q, Tendsto (fun n => normalizedPrimeNormCount (Ks (phi n)) (q+2))
        atTop (𝓝 (beta q))) ∧
      ∀ s : ℝ, 1 < s →
        Tendsto (fun n => Real.log (dedekindZeta (Ks (phi n)) s).re /
          (Module.finrank ℚ (Ks (phi n)) : ℝ)) atTop
          (𝓝 (∑' q, beta q*primeEulerLog (q+2) s)) := by
  obtain ⟨beta, phi, hphi, hbeta, hcounts⟩ := exists_subsequence_normalizedPrimeNormCount Ks
  exact ⟨beta, phi, hphi, hbeta, hcounts, fun s hs =>
    normalized_dedekindZeta_tendsto_of_primeNormCounts (fun n => Ks (phi n)) beta hcounts hs⟩

end UnitDistance.NumberFieldAnalysis
