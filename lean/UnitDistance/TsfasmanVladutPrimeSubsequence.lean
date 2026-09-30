module

public import UnitDistance.TsfasmanVladutBasicInequality
public import UnitDistance.PrimeNormCountLimits

@[expose] public section
set_option backward.privateInPublic true


/-!
# A common actual prime-budget and Euler-limit subsequence

For every sequence of actual number fields of growing degrees with bounded
root discriminants and eventually no real places, a single subsequence has
all the normalized prime-count limits, every real Euler logarithm limit
above one, and the proved unconditional Tsfasman–Vlăduţ prime budget.
-/

noncomputable section
open NumberField Filter Topology
open scoped BigOperators

namespace UnitDistance.NumberFieldAnalysis

/-- The limiting prime frequencies and budget exist; they need not be
supplied as extra asymptotic data for a number-field sequence. -/
theorem exists_subsequence_actual_tsfasmanVladut_prime_budget
    (Ks : ℕ → Type*) [∀ j, Field (Ks j)] [∀ j, NumberField (Ks j)]
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop)
    (hcomplex : ∀ᶠ j in atTop, InfinitePlace.nrRealPlaces (Ks j) = 0)
    {ell : ℝ}
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Ks j)) ≤ ell) :
    ∃ (beta : ℕ → ℝ) (phi : ℕ → ℕ), StrictMono phi ∧
      (∀ q, beta q ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ q, Tendsto (fun j => normalizedPrimeNormCount (Ks (phi j)) (q+2))
        atTop (𝓝 (beta q))) ∧
      (Summable (fun q : ℕ => beta q*primeBudgetWeight (q+2)) ∧
        (∑' q : ℕ, beta q*primeBudgetWeight (q+2)) ≤
          (ell-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/2) ∧
      ∀ s : ℝ, 1 < s →
        Tendsto (fun j => Real.log (dedekindZeta (Ks (phi j)) s).re /
          (Module.finrank ℚ (Ks (phi j)) : ℝ)) atTop
          (𝓝 (∑' q, beta q*primeEulerLog (q+2) s)) := by
  obtain ⟨beta, phi, hphi, hbeta, hcounts, hEuler⟩ :=
    exists_subsequence_normalized_dedekindZeta_limits Ks
  refine ⟨beta, phi, hphi, hbeta, hcounts, ?_, hEuler⟩
  exact actual_tsfasmanVladut_prime_budget (fun j => Ks (phi j)) beta hcounts
    (hdegree.comp hphi.tendsto_atTop) (hphi.tendsto_atTop.eventually hcomplex)
    (hphi.tendsto_atTop.eventually hdisc)

end UnitDistance.NumberFieldAnalysis
