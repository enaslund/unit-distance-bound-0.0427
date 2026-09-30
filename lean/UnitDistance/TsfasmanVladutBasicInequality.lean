module

public import UnitDistance.TsfasmanVladutPrimeSideRegroup
public import UnitDistance.TsfasmanVladutPrimeLimits
public import UnitDistance.TsfasmanVladutWeil

@[expose] public section
set_option backward.privateInPublic true


/-!
# The unconditional Tsfasman–Vlăduţ prime budget for actual number fields

Every analytic condition has been proved from the literal exponential-sech
kernel. The finite-field bound is obtained from the actual explicit formula
and actual prime-ideal series. Passing to a family uses only growing genuine
degrees, an eventual root-discriminant ceiling, and coordinatewise limits of
the actual normalized prime counts. No prime-budget or GRH premise remains.
-/

noncomputable section
open NumberField Filter Topology MeasureTheory Set
open scoped BigOperators

namespace UnitDistance.NumberFieldAnalysis

/-- The finite-prime version of the actual explicit-formula estimate, with
the contour parameter chosen internally from the damping parameter. -/
theorem tv_finite_primeNormCount_bound (K : Type*) [Field K] [NumberField K]
    (hcomplex : InfinitePlace.nrRealPlaces K = 0) {e : ℝ} (he : 0 < e) (J : Finset ℕ) :
    2*(∑ q ∈ J, (primeNormCount K (q+2) : ℝ)*tvPrimeWeight e (q+2)) ≤
      Real.log (absoluteDiscriminant K) + (Module.finrank ℚ K : ℝ)*
        (-(Real.eulerMascheroniConstant+Real.log (8*Real.pi))+
          ∫ x in Ioi (0:ℝ), tvArchIntegrand e x) + 4/e := by
  let a : ℝ := min (e/2) (1/4)
  have ha : 0 < a := lt_min (half_pos he) (by norm_num)
  have ha' : a ≤ 1/4 := min_le_right _ _
  have hae : a < e := (min_le_left _ _).trans_lt (half_lt_self he)
  have h := (mul_le_mul_of_nonneg_left
    (finite_primeNormCount_tvPrimeWeight_le_primeSideH K ha hae.le J) (by norm_num : (0:ℝ)≤2)).trans
      (tv_primeSide_bound K hcomplex he ha ha' hae)
  simpa only [absoluteDiscriminant_eq_abs, Int.cast_abs] using h

/-- The unconditional infinite prime budget for actual families of totally
complex number fields. Its summability is part of the conclusion. -/
theorem actual_tsfasmanVladut_prime_budget
    (Ks : ℕ → Type*) [∀ j, Field (Ks j)] [∀ j, NumberField (Ks j)]
    (beta : ℕ → ℝ)
    (hcounts : ∀ q, Tendsto (fun j => normalizedPrimeNormCount (Ks j) (q+2))
      atTop (𝓝 (beta q)))
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop)
    (hcomplex : ∀ᶠ j in atTop, InfinitePlace.nrRealPlaces (Ks j) = 0)
    {ell : ℝ}
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Ks j)) ≤ ell) :
    Summable (fun q : ℕ => beta q*primeBudgetWeight (q+2)) ∧
      (∑' q : ℕ, beta q*primeBudgetWeight (q+2)) ≤
        (ell-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/2 := by
  apply actual_primeNormCount_budget_of_tv_field_bounds Ks beta hcounts hdegree hdisc
  intro J
  filter_upwards [self_mem_nhdsWithin] with e he
  filter_upwards [hcomplex] with j hj
  exact tv_finite_primeNormCount_bound (Ks j) hj (show 0 < e from he) J

/-- The same actual budget with total complexity supplied by typeclasses. -/
theorem actual_tsfasmanVladut_prime_budget_totallyComplex
    (Ks : ℕ → Type*) [∀ j, Field (Ks j)] [∀ j, NumberField (Ks j)]
    [∀ j, IsTotallyComplex (Ks j)] (beta : ℕ → ℝ)
    (hcounts : ∀ q, Tendsto (fun j => normalizedPrimeNormCount (Ks j) (q+2))
      atTop (𝓝 (beta q)))
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop)
    {ell : ℝ}
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Ks j)) ≤ ell) :
    Summable (fun q : ℕ => beta q*primeBudgetWeight (q+2)) ∧
      (∑' q : ℕ, beta q*primeBudgetWeight (q+2)) ≤
        (ell-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/2 :=
  actual_tsfasmanVladut_prime_budget Ks beta hcounts hdegree
    (Eventually.of_forall fun j => IsTotallyComplex.nrRealPlaces_eq_zero (Ks j)) hdisc

end UnitDistance.NumberFieldAnalysis
