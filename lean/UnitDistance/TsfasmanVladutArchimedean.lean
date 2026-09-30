module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The unconditional prime-budget archimedean constant

The hyperbolic-secant test function has an exact archimedean integral
`log 2`, changing the Weil-formula constant `log (8*pi)` into `log (4*pi)`.
This file proves that integral directly by an antiderivative.
-/

noncomputable section
open Filter Topology MeasureTheory

namespace UnitDistance.NumberFieldAnalysis

/-- The limiting complex-place integral in the unconditional test function. -/
def tvArchBase (x : ℝ) : ℝ :=
  1 / (2*Real.sinh (x/2)) * (1 - 1/Real.cosh (x/2))

/-- An antiderivative tending to zero at positive infinity. -/
def tvArchPrimitive (x : ℝ) : ℝ :=
  -Real.log (1 + 1/Real.cosh (x/2))

theorem tvArchBase_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ tvArchBase x := by
  have hc := Real.cosh_pos (x/2)
  have hle : 1 / Real.cosh (x/2) ≤ 1 := by
    rw [div_le_iff₀ hc, one_mul]
    exact Real.one_le_cosh _
  unfold tvArchBase
  have hs := Real.sinh_pos_iff.mpr (half_pos hx)
  positivity

theorem hasDerivAt_tvArchPrimitive {x : ℝ} (hx : 0 < x) :
    HasDerivAt tvArchPrimitive (tvArchBase x) x := by
  have hc := Real.cosh_pos (x/2)
  have hs := Real.sinh_pos_iff.mpr (half_pos hx)
  have hcosh := (Real.hasDerivAt_cosh (x/2)).comp x ((hasDerivAt_id x).div_const 2)
  have h := ((hcosh.inv hc.ne').const_add 1).log (by positivity :
    1 + (Real.cosh (x/2))⁻¹ ≠ 0)
  convert! h.neg using 1
  · ext y
    simp [tvArchPrimitive, one_div]
  · unfold tvArchBase
    dsimp only [Function.comp_apply, id_eq, Pi.inv_apply]
    field_simp [hc.ne', hs.ne']
    nlinarith [Real.cosh_sq (x/2)]

theorem continuous_tvArchPrimitive : Continuous tvArchPrimitive := by
  unfold tvArchPrimitive
  fun_prop (disch := intro x; positivity)

theorem tendsto_inv_cosh_half_atTop :
    Tendsto (fun x : ℝ => (Real.cosh (x/2))⁻¹) atTop (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => Real.exp (x/2)/2) atTop atTop :=
    ((Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))).atTop_div_const
      (by norm_num : (0:ℝ)<2))
  have hc : Tendsto (fun x : ℝ => Real.cosh (x/2)) atTop atTop := by
    apply tendsto_atTop_mono (fun x => ?_) he
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(x/2))]
  exact tendsto_inv_atTop_zero.comp hc

theorem tendsto_tvArchPrimitive_atTop : Tendsto tvArchPrimitive atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => 1 + (Real.cosh (x/2))⁻¹) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_inv_cosh_half_atTop.const_add 1
  have h := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hbase
  change Tendsto (fun x : ℝ => -Real.log (1 + 1/Real.cosh (x/2))) atTop (𝓝 0)
  simpa only [Function.comp_apply, Real.log_one, neg_zero, one_div] using h.neg

theorem integrableOn_tvArchBase : IntegrableOn tvArchBase (Set.Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg continuous_tvArchPrimitive.continuousWithinAt
    (fun _ hx => hasDerivAt_tvArchPrimitive hx) (fun _ hx => tvArchBase_nonneg hx)
    tendsto_tvArchPrimitive_atTop

/-- Exact archimedean integral for the unconditional hyperbolic-secant test. -/
theorem integral_tvArchBase : (∫ x in Set.Ioi (0:ℝ), tvArchBase x) = Real.log 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    continuous_tvArchPrimitive.continuousWithinAt
    (fun _ hx => hasDerivAt_tvArchPrimitive hx) (fun _ hx => tvArchBase_nonneg hx)
    tendsto_tvArchPrimitive_atTop
  norm_num [tvArchPrimitive] at h ⊢
  exact h

/-- An integrable error profile for the regularized archimedean integral. -/
def tvArchError (x : ℝ) : ℝ := x / Real.sinh x

theorem tvArchError_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ tvArchError x :=
  div_nonneg hx.le (Real.sinh_pos_iff.mpr hx).le

theorem tvArchError_le {x : ℝ} (hx : 0 < x) :
    tvArchError x ≤ (1+2*x)*Real.exp (-x) := by
  have hs := Real.sinh_pos_iff.mpr hx
  have he := Real.exp_pos x
  have hexp := Real.add_one_le_exp (2*x)
  rw [show 2*x = x+x by ring, Real.exp_add] at hexp
  unfold tvArchError
  rw [div_le_iff₀ hs, Real.sinh_eq, Real.exp_neg]
  field_simp
  nlinarith

theorem integrableOn_tvArchError : IntegrableOn tvArchError (Set.Ioi 0) := by
  have he : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) (0:ℝ)
  have hxe : IntegrableOn (fun x : ℝ => x*Real.exp (-x)) (Set.Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_rpow (p := (1:ℝ)) (s := (1:ℝ))
        (by norm_num) (by norm_num))
  have hmajor : IntegrableOn (fun x : ℝ => (1+2*x)*Real.exp (-x)) (Set.Ioi 0) := by
    convert! he.add (hxe.const_mul 2) using 1
    ext x
    simp only [Pi.add_apply]
    ring
  refine hmajor.mono' ?_ ?_
  · have hm : Measurable tvArchError := by
      unfold tvArchError
      fun_prop
    exact hm.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (tvArchError_nonneg hx)]
    exact tvArchError_le hx

/-- The regularized archimedean integrand for `exp(-e*x)/cosh(x/2)`. -/
def tvArchIntegrand (e x : ℝ) : ℝ :=
  1/(2*Real.sinh (x/2)) * (1-Real.exp (-e*x)/Real.cosh (x/2))

theorem tvArchIntegrand_sub {e x : ℝ} (hx : 0 < x) :
    tvArchIntegrand e x - tvArchBase x =
      (1-Real.exp (-e*x)) / Real.sinh x := by
  have hs := Real.sinh_pos_iff.mpr (half_pos hx)
  have hc := Real.cosh_pos (x/2)
  have hdouble : Real.sinh x = 2*Real.sinh (x/2)*Real.cosh (x/2) := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using
      (Real.sinh_two_mul (x/2))
  unfold tvArchIntegrand tvArchBase
  rw [hdouble]
  field_simp
  ring

theorem tvArchIntegrand_bounds {e x : ℝ} (he : 0 ≤ e) (hx : 0 < x) :
    tvArchBase x ≤ tvArchIntegrand e x ∧
      tvArchIntegrand e x ≤ tvArchBase x + e*tvArchError x := by
  have hs := Real.sinh_pos_iff.mpr hx
  have hexp : Real.exp (-e*x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hlo : 0 ≤ (1-Real.exp (-e*x))/Real.sinh x := by positivity
  have hup : (1-Real.exp (-e*x))/Real.sinh x ≤ e*tvArchError x := by
    unfold tvArchError
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hs]
    linarith [Real.add_one_le_exp (-e*x)]
  have h := tvArchIntegrand_sub (e := e) hx
  constructor <;> linarith

theorem integrableOn_tvArchIntegrand {e : ℝ} (he : 0 ≤ e) :
    IntegrableOn (tvArchIntegrand e) (Set.Ioi 0) := by
  refine (integrableOn_tvArchBase.add (integrableOn_tvArchError.const_mul e)).mono' ?_ ?_
  · unfold tvArchIntegrand
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro x hx
    have hb := tvArchIntegrand_bounds he hx
    rw [Real.norm_eq_abs, abs_of_nonneg ((tvArchBase_nonneg hx).trans hb.1)]
    exact hb.2

/-- The complete archimedean integral and a finite linear error bound. -/
theorem integral_tvArchIntegrand_bounds {e : ℝ} (he : 0 ≤ e) :
    Real.log 2 ≤ ∫ x in Set.Ioi (0:ℝ), tvArchIntegrand e x ∧
      (∫ x in Set.Ioi (0:ℝ), tvArchIntegrand e x) ≤
        Real.log 2 + e*(∫ x in Set.Ioi (0:ℝ), tvArchError x) := by
  constructor
  · rw [← integral_tvArchBase]
    refine integral_mono_ae integrableOn_tvArchBase (integrableOn_tvArchIntegrand he) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    exact fun x hx => (tvArchIntegrand_bounds he hx).1
  · rw [← integral_tvArchBase, ← integral_const_mul,
      ← integral_add integrableOn_tvArchBase (integrableOn_tvArchError.const_mul e)]
    refine integral_mono_ae (integrableOn_tvArchIntegrand he)
      (integrableOn_tvArchBase.add (integrableOn_tvArchError.const_mul e)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    exact fun x hx => (tvArchIntegrand_bounds he hx).2

/-- The precise archimedean boundary constant is obtained without numerical
integration or a hypothesis about the test function. -/
theorem tendsto_integral_tvArchIntegrand :
    Tendsto (fun e : ℝ => ∫ x in Set.Ioi (0:ℝ), tvArchIntegrand e x)
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun e : ℝ => Real.log 2 + e*(∫ x in Set.Ioi (0:ℝ), tvArchError x))
      (𝓝[>] 0) (𝓝 (Real.log 2)) from by
        have h₀ : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 (0:ℝ)) :=
          continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
        have h := h₀.mul_const (∫ x in Set.Ioi (0:ℝ), tvArchError x)
        simpa only [zero_mul, add_zero] using h.const_add (Real.log 2))
  · filter_upwards [self_mem_nhdsWithin] with e he
    exact (integral_tvArchIntegrand_bounds (le_of_lt he)).1
  · filter_upwards [self_mem_nhdsWithin] with e he
    exact (integral_tvArchIntegrand_bounds (le_of_lt he)).2

end UnitDistance.NumberFieldAnalysis
