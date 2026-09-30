module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.privateInPublic true


open Complex Set Filter Asymptotics MeasureTheory
open scoped Topology Real
namespace UnitDistance.NumberFieldAnalysis

/- The next elementary asymptotic proof is adapted from AINTLIB, Chris Birkbeck,
Apache-2.0; pin and license are recorded in third-party/aintlib. -/
/-- A stretched-exponential `exp(-c·x^p)` beats every power at infinity. -/
theorem hecke_isBigO_exp_neg_rpow {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (r : ℝ) :
    (fun x : ℝ => Real.exp (-c * x ^ p)) =O[atTop] fun x : ℝ => x ^ r := by
  have h1 : (fun y : ℝ => y ^ (-r / p)) =O[atTop] (fun y => Real.exp (c * y)) :=
    (isLittleO_rpow_exp_pos_mul_atTop (-r / p) hc).isBigO
  obtain ⟨C, hC⟩ := h1.bound
  have htend : Filter.Tendsto (fun x : ℝ => x ^ p) atTop atTop := tendsto_rpow_atTop hp
  have hev := htend.eventually hC
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop (1:ℝ)] with x hx h1x
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos h1x
  have hxr_pos : (0:ℝ) < x ^ r := Real.rpow_pos_of_pos hx0 _
  have hexp_pos : (0:ℝ) < Real.exp (c * x ^ p) := Real.exp_pos _
  have hxp : (x ^ p) ^ (-r / p) = x ^ (-r) := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hx ⊢
  rw [hxp, Real.rpow_neg hx0.le, abs_of_pos (by positivity), abs_of_pos hexp_pos] at hx
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos hxr_pos]
  have h2 : 1 ≤ C * Real.exp (c * x ^ p) * x ^ r := by
    have h3 := mul_le_mul_of_nonneg_right hx hxr_pos.le
    rwa [inv_mul_cancel₀ hxr_pos.ne'] at h3
  have h4 : Real.exp (-c * x ^ p) = (Real.exp (c * x ^ p))⁻¹ := by
    rw [show -c * x ^ p = -(c * x ^ p) by ring, Real.exp_neg]
  rw [h4]
  calc (Real.exp (c * x ^ p))⁻¹ = (Real.exp (c * x ^ p))⁻¹ * 1 := (mul_one _).symm
    _ ≤ (Real.exp (c * x ^ p))⁻¹ * (C * Real.exp (c * x ^ p) * x ^ r) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C * x ^ r := by field_simp


/-- An explicit stretched-exponential bound at infinity implies every power bound. -/
theorem isBigO_rpow_atTop_of_stretched_exp {f : ℝ → ℂ} {C k r : ℝ}
    (hk : 0 < k) (hr : 0 < r)
    (h : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-k*t^r)) (q : ℝ) :
    f =O[atTop] (fun t : ℝ => t^q) := by
  have h₁ : f =O[atTop] (fun t : ℝ => Real.exp (-k*t^r)) := by
    rw [isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [Real.norm_eq_abs, Real.abs_exp] using h t ht
  exact h₁.trans (hecke_isBigO_exp_neg_rpow hk hr q)

/-- A polynomial prefactor cannot prevent inverse stretched-exponential decay at zero. -/
theorem isBigO_rpow_nhdsGT_zero_of_stretched_exp {f : ℝ → ℂ} {C k r b : ℝ}
    (hk : 0 < k) (hr : 0 < r)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖f t‖ ≤ C*t^b * Real.exp (-k*t^(-r))) (q : ℝ) :
    f =O[𝓝[>] 0] (fun t : ℝ => t^q) := by
  have h₁ : f =O[𝓝[>] 0] (fun t : ℝ => t^b * Real.exp (-k*t^(-r))) := by
    rw [isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    change 0 < t at ht
    have hb : 0 < t^b := Real.rpow_pos_of_pos ht b
    simpa only [Real.norm_eq_abs, abs_of_pos (mul_pos hb (Real.exp_pos _)), mul_assoc] using h t ht ht1.le
  have h₂ : (fun x : ℝ => x^(-b) * Real.exp (-k*x^r)) =O[atTop]
      (fun x : ℝ => x^(-q)) := by
    have ho := (isBigO_refl (fun x : ℝ => x^(-b)) atTop).mul
      (hecke_isBigO_exp_neg_rpow hk hr (b-q))
    refine ho.congr' Filter.EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have h₃ := h₂.comp_tendsto tendsto_inv_nhdsGT_zero
  apply h₁.trans
  refine h₃.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    dsimp only [Function.comp_apply]
    rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv,
      Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    dsimp only [Function.comp_apply]
    rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv]

/-- The same explicit bounds give absolute Mellin convergence at every complex parameter. -/
theorem mellinConvergent_of_two_sided_stretched_exp {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioi 0)) {C₁ C₂ k₁ k₂ r₁ r₂ b : ℝ}
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hTop : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C₁ * Real.exp (-k₁*t^r₁))
    (h₀ : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖f t‖ ≤ C₂*t^b * Real.exp (-k₂*t^(-r₂)))
    (s : ℂ) : MellinConvergent f s := by
  exact mellinConvergent_of_isBigO_rpow (hf.locallyIntegrableOn measurableSet_Ioi)
    (isBigO_rpow_atTop_of_stretched_exp hk₁ hr₁ hTop (-(s.re+1))) (by linarith)
    (isBigO_rpow_nhdsGT_zero_of_stretched_exp hk₂ hr₂ h₀ (-(s.re-1))) (by linarith)

/-- Two-sided explicit stretched-exponential theta estimates give an entire Mellin transform. -/
theorem differentiable_mellin_of_two_sided_stretched_exp {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioi 0)) {C₁ C₂ k₁ k₂ r₁ r₂ b : ℝ}
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hTop : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C₁ * Real.exp (-k₁*t^r₁))
    (h₀ : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖f t‖ ≤ C₂*t^b * Real.exp (-k₂*t^(-r₂))) :
    Differentiable ℂ (mellin f) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow (hf.locallyIntegrableOn measurableSet_Ioi)
    (isBigO_rpow_atTop_of_stretched_exp hk₁ hr₁ hTop (-(s.re+1))) (by linarith)
    (isBigO_rpow_nhdsGT_zero_of_stretched_exp hk₂ hr₂ h₀ (-(s.re-1))) (by linarith)

end UnitDistance.NumberFieldAnalysis
