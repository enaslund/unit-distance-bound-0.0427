module

public import UnitDistance.TsfasmanVladutPrimeSubsequence
public import UnitDistance.RelativeHeckeComparison

@[expose] public section
set_option backward.privateInPublic true


/-!
# Full-family relative-residue bounds from the actual prime budget

An exceptional subsequence would have a further subsequence with all actual
prime frequencies and the unconditional Tsfasman–Vlăduţ budget. The elementary
Euler debit and the completed-function comparison then contradict every
exception. Neither prime-frequency limits nor a Basic Inequality are inputs.
-/

noncomputable section
open NumberField Filter Topology
open scoped BigOperators
namespace UnitDistance.NumberFieldAnalysis

variable (Ks Fs : ℕ → Type*)
  [∀ n, Field (Ks n)] [∀ n, NumberField (Ks n)]
  [∀ n, Field (Fs n)] [∀ n, NumberField (Fs n)]
  [∀ n, Algebra (Fs n) (Ks n)]

/-- The two-limit passage only needs an eventual completed-function
comparison at each positive abscissa; the exceptional finite initial part
may depend on that abscissa. -/
theorem eventual_normalized_log_relativeResidue_lt_of_eventual_comparison
    (hquad : ∀ n, Module.finrank (Fs n) (Ks n) = 2) (ell : ℝ)
    (Z : ℝ → ℝ) {C T : ℝ}
    (hcomp : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      relativeCompletedReal (Ks n) (Fs n) ell 1 ≤
        relativeCompletedReal (Ks n) (Fs n) ell (1+eta))
    (hz : ∀ eta : ℝ, 0 < eta →
      Tendsto (fun n => Real.log (dedekindZeta (Ks n) (1+eta)).re /
        (2*(Module.finrank ℚ (Fs n) : ℝ))) atTop (𝓝 (Z eta)))
    (hboundary : Tendsto Z (𝓝[>] 0) (𝓝 C)) (hCT : C < T) :
    ∀ᶠ n in atTop, Real.log (relativeResidue (Ks n) (Fs n)) /
      (Module.finrank ℚ (Fs n) : ℝ) < T := by
  have hlim : Tendsto (fun eta => Z eta+relativeGammaError ell eta)
      (𝓝[>] 0) (𝓝 C) := by
    simpa using hboundary.add
      ((tendsto_relativeGammaError_zero ell).mono_left nhdsWithin_le_nhds)
  have hpos : ∀ᶠ eta : ℝ in 𝓝[>] 0, 0 < eta := self_mem_nhdsWithin
  obtain ⟨eta, heta, hsmall⟩ := (hpos.and (hlim.eventually_lt_const hCT)).exists
  have hfixed := (hz eta heta).add_const (relativeGammaError ell eta)
  filter_upwards [hfixed.eventually_lt_const hsmall, hcomp eta heta] with n hn hc
  have hfinite := normalized_log_relativeResidue_le_zeta_of_completion_le
    (Ks n) (Fs n) (hquad n) ell heta hc
  apply lt_of_le_of_lt hfinite
  apply lt_of_le_of_lt _ hn
  exact add_le_add le_rfl ((le_abs_self _).trans
    (abs_relativeGammaCorrection_le ell eta (complexPlaceRatio_mem (Fs n))))

/-- The actual analytic family transfer. `hY` and `hR` are uniform finite-field
Euler/remainder bounds, discharged by inheritance from an actual fixed base
in `RelativeResidueFixedBase`. The completed-function comparison remains
explicit and is independent of the prime-budget proof. -/
theorem eventual_normalized_log_relativeResidue_lt_of_prime_budget
    (hquad : ∀ n, Module.finrank (Fs n) (Ks n) = 2)
    (hdegree : Tendsto (fun n => Module.finrank ℚ (Ks n)) atTop atTop)
    (hcomplex : ∀ᶠ n in atTop, InfinitePlace.nrRealPlaces (Ks n) = 0)
    {ell epsilon Y R T : ℝ} (hepsilon : 0 < epsilon)
    (hdisc : ∀ᶠ n in atTop, Real.log (rootDiscriminant (Ks n)) ≤ ell)
    (hcomp : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      relativeCompletedReal (Ks n) (Fs n) ell 1 ≤
        relativeCompletedReal (Ks n) (Fs n) ell (1+eta))
    (hY : ∀ᶠ n in atTop,
      Real.log (dedekindZeta (Ks n) (1+epsilon)).re /
        (Module.finrank ℚ (Ks n) : ℝ) ≤ Y)
    (hR : ∀ J : Finset ℕ, ∀ᶠ n in atTop,
      (∑ q ∈ J, normalizedPrimeNormCount (Ks n) (q+2)*
        (Real.log (q+2)/(((q+2:ℕ):ℝ)^2-1))) ≤ R)
    (hceiling : Y+epsilon*((ell-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4+R) < T) :
    ∀ᶠ n in atTop, Real.log (relativeResidue (Ks n) (Fs n)) /
      (Module.finrank ℚ (Fs n) : ℝ) < T := by
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop,
      T ≤ Real.log (relativeResidue (Ks n) (Fs n))/(Module.finrank ℚ (Fs n) : ℝ) := by
    simpa only [not_lt] using (Filter.not_eventually.mp hnot)
  obtain ⟨ns, hns, hbad⟩ := Filter.exists_seq_forall_of_frequently hfreq
  obtain ⟨beta, phi, hphi, hbeta, hcounts, hbudget, hEuler⟩ :=
    exists_subsequence_actual_tsfasmanVladut_prime_budget (fun n => Ks (ns n))
      (hdegree.comp hns) (hns.eventually hcomplex) (hns.eventually hdisc)
  have hsub : Tendsto (fun n => ns (phi n)) atTop atTop :=
    hns.comp hphi.tendsto_atTop
  have hpos : ∀ q : ℕ, 1 < q+2 := by omega
  have hbeta0 : ∀ q, 0 ≤ beta q := fun q => (hbeta q).1
  have hEulerSum : Summable (fun q : ℕ => beta q*primeEulerLog (q+2) (1+epsilon)) := by
    apply (summable_primeEulerLog_all_norms (by linarith : 1<1+epsilon)).of_nonneg_of_le
    · intro q
      exact mul_nonneg (hbeta0 q) (primeEulerLog_nonneg (hpos q) (by linarith))
    · intro q
      exact mul_le_of_le_one_left (primeEulerLog_nonneg (hpos q) (by linarith)) (hbeta q).2
  have hYlim : (∑' q : ℕ, beta q*primeEulerLog (q+2) (1+epsilon)) ≤ Y :=
    le_of_tendsto (hEuler (1+epsilon) (by linarith)) (by
      simpa only [Complex.ofReal_add, Complex.ofReal_one] using hsub.eventually hY)
  have hYfinite : ∀ J : Finset ℕ,
      (∑ q ∈ J, beta q*primeEulerLog (q+2) (1+epsilon)) ≤ Y := by
    intro J
    exact (hEulerSum.sum_le_tsum J (fun q _ =>
      mul_nonneg (hbeta0 q) (primeEulerLog_nonneg (hpos q) (by linarith)))).trans hYlim
  have hBfinite : ∀ J : Finset ℕ,
      (∑ q ∈ J, beta q*primeBudgetWeight (q+2)) ≤
        (ell-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/2 := by
    intro J
    exact (hbudget.1.sum_le_tsum J (fun q _ => mul_nonneg (hbeta0 q)
      (primeBudgetWeight_nonneg (by exact_mod_cast hpos q)))).trans hbudget.2
  have hRfinite : ∀ J : Finset ℕ,
      (∑ q ∈ J, beta q*(Real.log (q+2)/(((q+2:ℕ):ℝ)^2-1))) ≤ R := by
    intro J
    apply le_of_tendsto _ (hsub.eventually (hR J))
    exact tendsto_finsetSum J (fun q _ => (hcounts q).mul_const _)
  obtain ⟨hboundarySum, hboundaryBound⟩ := primeBudget_tsum_le
    (fun q : ℕ => q+2) beta hpos hbeta0 hepsilon.le hYfinite (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hBfinite)
      (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hRfinite)
  have hbound : (∑' q : ℕ, beta q*primeEulerLog (q+2) 1) < T := by
    apply hboundaryBound.trans_lt
    simpa only [div_div, show (2:ℝ)*2=4 by norm_num] using hceiling
  have hgood := eventual_normalized_log_relativeResidue_lt_of_eventual_comparison
    (fun n => Ks (ns (phi n))) (fun n => Fs (ns (phi n)))
    (fun n => hquad (ns (phi n))) ell
    (fun eta => ∑' q : ℕ, beta q*primeEulerLog (q+2) (1+eta))
    (fun eta heta => hsub.eventually (hcomp eta heta))
    (fun eta heta => ?_) (tendsto_primeEulerLog_tsum_boundary
      (fun q : ℕ => q+2) beta hpos hbeta0 hboundarySum) hbound
  · obtain ⟨n, hn⟩ := hgood.exists
    exact (not_lt_of_ge (hbad (phi n))) hn
  · have he := hEuler (1+eta) (by linarith)
    convert he using 1
    funext n
    have hd := Module.finrank_mul_finrank ℚ (Fs (ns (phi n))) (Ks (ns (phi n)))
    rw [hquad] at hd
    have hdreal : (2:ℝ)*Module.finrank ℚ (Fs (ns (phi n))) =
        Module.finrank ℚ (Ks (ns (phi n))) := by
      exact_mod_cast (by omega : 2*Module.finrank ℚ (Fs (ns (phi n))) =
        Module.finrank ℚ (Ks (ns (phi n))))
    simp only [hdreal, Complex.ofReal_add, Complex.ofReal_one]

end UnitDistance.NumberFieldAnalysis
