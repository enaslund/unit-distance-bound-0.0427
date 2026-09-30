module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import UnitDistance.TsfasmanVladutPrimeWeight
public import UnitDistance.PrimeNormCounts
public import UnitDistance.RelativeDiscriminant
public import UnitDistance.TsfasmanVladutArchimedean

@[expose] public section
set_option backward.privateInPublic true


/-!
# Degree normalization and the actual prime-count budget limit

The finite-field analytic inequality is kept as an explicit premise. This
module carries it through the two limits: first the degrees of actual
number fields tend to infinity at fixed positive damping, then damping
tends to zero on every finite set of norms. The infinite budget and its
summability follow from nonnegativity, rather than an assumed interchange
of infinite prime sums and limits.
-/

noncomputable section
open NumberField Filter Topology
open scoped BigOperators

namespace UnitDistance.NumberFieldAnalysis

theorem tv_log_rootDiscriminant (K : Type*) [Field K] [NumberField K] :
    Real.log (rootDiscriminant K) =
      Real.log (absoluteDiscriminant K)/(Module.finrank ℚ K : ℝ) := by
  rw [rootDiscriminant, Real.log_rpow (absoluteDiscriminant_pos K)]
  ring

variable (Ks : ℕ → Type*) [∀ j, Field (Ks j)] [∀ j, NumberField (Ks j)]

/-- Actual normalized prime counts have nonnegative coordinatewise limits. -/
theorem primeNormCount_limit_nonneg (beta : ℕ → ℝ)
    (hcounts : ∀ q, Tendsto (fun j => normalizedPrimeNormCount (Ks j) (q+2))
      atTop (𝓝 (beta q))) (q : ℕ) : 0 ≤ beta q :=
  le_of_tendsto_of_tendsto tendsto_const_nhds (hcounts q)
    (Eventually.of_forall fun j => (normalizedPrimeNormCount_mem (Ks j) (by omega)).1)

/-- Fixed damping: division by the genuine field degree removes every
field-independent pole term. The discriminant contribution is the actual
logarithmic root discriminant. -/
theorem finite_tvPrimeWeight_limit_le (beta : ℕ → ℝ)
    (hcounts : ∀ q, Tendsto (fun j => normalizedPrimeNormCount (Ks j) (q+2))
      atTop (𝓝 (beta q)))
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop)
    {ell e arch pole : ℝ}
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Ks j)) ≤ ell)
    (J : Finset ℕ)
    (hfield : ∀ᶠ j in atTop,
      2*(∑ q ∈ J, (primeNormCount (Ks j) (q+2) : ℝ)*tvPrimeWeight e (q+2)) ≤
        Real.log (absoluteDiscriminant (Ks j)) +
          (Module.finrank ℚ (Ks j) : ℝ)*arch + pole) :
    ∑ q ∈ J, beta q*tvPrimeWeight e (q+2) ≤ (ell+arch)/2 := by
  have hd : Tendsto (fun j => (Module.finrank ℚ (Ks j) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdegree
  have hleft : Tendsto
      (fun j => 2*(∑ q ∈ J, normalizedPrimeNormCount (Ks j) (q+2)*tvPrimeWeight e (q+2)))
      atTop (𝓝 (2*(∑ q ∈ J, beta q*tvPrimeWeight e (q+2)))) :=
    (tendsto_finsetSum J (fun q _ => (hcounts q).mul_const _)).const_mul 2
  have hright : Tendsto
      (fun j => ell+arch+pole/(Module.finrank ℚ (Ks j) : ℝ)) atTop (𝓝 (ell+arch)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hd) :
        Tendsto (fun j => ell+arch+pole/(Module.finrank ℚ (Ks j) : ℝ))
          atTop (𝓝 (ell+arch+0)))
  have hbound : ∀ᶠ j in atTop,
      2*(∑ q ∈ J, normalizedPrimeNormCount (Ks j) (q+2)*tvPrimeWeight e (q+2)) ≤
        ell+arch+pole/(Module.finrank ℚ (Ks j) : ℝ) := by
    filter_upwards [hdisc, hfield] with j hj hjfield
    have hjpos : (0:ℝ) < Module.finrank ℚ (Ks j) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := Ks j)
    rw [tv_log_rootDiscriminant] at hj
    have heq :
        2*(∑ q ∈ J, normalizedPrimeNormCount (Ks j) (q+2)*tvPrimeWeight e (q+2)) =
          (2*(∑ q ∈ J, (primeNormCount (Ks j) (q+2) : ℝ)*tvPrimeWeight e (q+2)))/
            (Module.finrank ℚ (Ks j) : ℝ) := by
      rw [div_eq_mul_inv, mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      unfold normalizedPrimeNormCount
      ring
    rw [heq]
    calc
      _ ≤ (Real.log (absoluteDiscriminant (Ks j))+
          (Module.finrank ℚ (Ks j) : ℝ)*arch+pole)/(Module.finrank ℚ (Ks j) : ℝ) :=
        div_le_div_of_nonneg_right hjfield hjpos.le
      _ = Real.log (absoluteDiscriminant (Ks j))/(Module.finrank ℚ (Ks j) : ℝ)+
          arch+pole/(Module.finrank ℚ (Ks j) : ℝ) := by
        field_simp
      _ ≤ _ := by linarith
  have h := le_of_tendsto_of_tendsto hleft hright hbound
  linarith

/-- Actual degree-normalized prime counts obey the undamped basic budget
whenever the finite-field analytic inequalities and archimedean limit hold.
The only arithmetic asymptotic inputs are the displayed count convergence,
degree growth, and root-discriminant bound. -/
theorem actual_primeNormCount_budget_of_finite_field_bounds (beta : ℕ → ℝ)
    (hcounts : ∀ q, Tendsto (fun j => normalizedPrimeNormCount (Ks j) (q+2))
      atTop (𝓝 (beta q)))
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop)
    {ell archLimit : ℝ} {arch pole : ℝ → ℝ}
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Ks j)) ≤ ell)
    (harch : Tendsto arch (𝓝[>] 0) (𝓝 archLimit))
    (hfield : ∀ J : Finset ℕ, ∀ᶠ e : ℝ in 𝓝[>] 0, ∀ᶠ j in atTop,
      2*(∑ q ∈ J, (primeNormCount (Ks j) (q+2) : ℝ)*tvPrimeWeight e (q+2)) ≤
        Real.log (absoluteDiscriminant (Ks j)) +
          (Module.finrank ℚ (Ks j) : ℝ)*arch e + pole e) :
    Summable (fun q : ℕ => beta q*primeBudgetWeight (q+2)) ∧
      (∑' q : ℕ, beta q*primeBudgetWeight (q+2)) ≤ (ell+archLimit)/2 := by
  apply primeBudget_summable_le_of_tvPrimeWeight
    (fun q : ℕ => (q+2:ℝ)) beta (fun q => by have := Nat.cast_nonneg (α := ℝ) q; linarith)
    (primeNormCount_limit_nonneg Ks beta hcounts)
    ((harch.const_add ell).div_const 2)
  intro J
  filter_upwards [hfield J] with e he
  exact finite_tvPrimeWeight_limit_le Ks beta hcounts hdegree hdisc J he

/-- The exact unconditional constant for the hyperbolic-secant test. The
finite-field premise is the one supplied by the explicit formula for a
totally complex field; no field inequality is postulated by this theorem. -/
theorem actual_primeNormCount_budget_of_tv_field_bounds (beta : ℕ → ℝ)
    (hcounts : ∀ q, Tendsto (fun j => normalizedPrimeNormCount (Ks j) (q+2))
      atTop (𝓝 (beta q)))
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop)
    {ell : ℝ}
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Ks j)) ≤ ell)
    (hfield : ∀ J : Finset ℕ, ∀ᶠ e : ℝ in 𝓝[>] 0, ∀ᶠ j in atTop,
      2*(∑ q ∈ J, (primeNormCount (Ks j) (q+2) : ℝ)*tvPrimeWeight e (q+2)) ≤
        Real.log (absoluteDiscriminant (Ks j)) + (Module.finrank ℚ (Ks j) : ℝ)*
          (-(Real.eulerMascheroniConstant+Real.log (8*Real.pi))+
            ∫ x in Set.Ioi (0:ℝ), tvArchIntegrand e x) + 4/e) :
    Summable (fun q : ℕ => beta q*primeBudgetWeight (q+2)) ∧
      (∑' q : ℕ, beta q*primeBudgetWeight (q+2)) ≤
        (ell-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/2 := by
  have h := actual_primeNormCount_budget_of_finite_field_bounds Ks beta hcounts hdegree
    hdisc (tendsto_integral_tvArchIntegrand.const_add
      (-(Real.eulerMascheroniConstant+Real.log (8*Real.pi)))) hfield
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [show Real.log (8*Real.pi) = Real.log 2+Real.log (4*Real.pi) by
    rw [show (8:ℝ)*Real.pi = 2*(4*Real.pi) by ring,
      Real.log_mul (by norm_num : (2:ℝ)≠0) (by positivity : (4:ℝ)*Real.pi≠0)]]
  ring

end UnitDistance.NumberFieldAnalysis
