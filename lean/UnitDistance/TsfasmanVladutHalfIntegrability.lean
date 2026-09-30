module

public import UnitDistance.TsfasmanVladutHalfProfile
public import Mathlib.MeasureTheory.Integral.ExpDecay

@[expose] public section
set_option backward.privateInPublic true


/-! Integrability and vanishing at infinity of the actual smooth branches. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace UnitDistance.NumberFieldAnalysis

theorem tvHalf_integrable_of_bound {f : ℝ → ℝ} {b C : ℝ}
    (hb : 0 < b) (hf : Continuous f)
    (hbound : ∀ x : ℝ, 0 ≤ x → |f x| ≤ C*Real.exp (-b*x)) :
    IntegrableOn f (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 hb).const_mul C).mono'
    hf.aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall (fun x hx => by simpa only [Real.norm_eq_abs, neg_mul] using hbound x hx.le))

theorem tvHalf_tendsto_zero_of_bound {f : ℝ → ℝ} {b C : ℝ}
    (hb : 0 < b) (hbound : ∀ x : ℝ, 0 ≤ x → |f x| ≤ C*Real.exp (-b*x)) :
    Tendsto f atTop (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-b*x)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)
    simpa only [Function.comp_def, id_eq, neg_mul] using h
  apply squeeze_zero_norm' ?_ (by simpa using he.const_mul C)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  simpa only [Real.norm_eq_abs, neg_mul] using hbound x hx

theorem integrableOn_tvHalfProfile {b : ℝ} (hb : 0 < b+1/2) :
    IntegrableOn (tvHalfProfile b) (Ioi 0) := by
  apply tvHalf_integrable_of_bound hb (continuous_tvHalfProfile b) (C := 2)
  intro x hx
  simpa only [abs_of_pos (tvHalfProfile_pos b x)] using tvHalfProfile_bound b hx

theorem integrableOn_tvHalfDeriv {b : ℝ} (hb : 0 < b+1/2) :
    IntegrableOn (tvHalfDeriv b) (Ioi 0) := by
  apply tvHalf_integrable_of_bound hb (continuous_tvHalfDeriv b) (C := 2*(|b|+1/2))
  intro x hx
  simpa only [mul_assoc, mul_comm, mul_left_comm] using abs_tvHalfDeriv_bound b hx

theorem integrableOn_tvHalfSecond {b : ℝ} (hb : 0 < b+1/2) :
    IntegrableOn (tvHalfSecond b) (Ioi 0) := by
  apply tvHalf_integrable_of_bound hb (continuous_tvHalfSecond b) (C := 2*((|b|+1/2)^2+1/4))
  intro x hx
  simpa only [mul_assoc, mul_comm, mul_left_comm] using abs_tvHalfSecond_bound b hx

theorem tendsto_tvHalfProfile_atTop {b : ℝ} (hb : 0 < b+1/2) :
    Tendsto (tvHalfProfile b) atTop (𝓝 0) := by
  apply tvHalf_tendsto_zero_of_bound hb (C := 2)
  intro x hx
  simpa only [abs_of_pos (tvHalfProfile_pos b x)] using tvHalfProfile_bound b hx

theorem tendsto_tvHalfDeriv_atTop {b : ℝ} (hb : 0 < b+1/2) :
    Tendsto (tvHalfDeriv b) atTop (𝓝 0) := by
  apply tvHalf_tendsto_zero_of_bound hb (C := 2*(|b|+1/2))
  intro x hx
  simpa only [mul_assoc, mul_comm, mul_left_comm] using abs_tvHalfDeriv_bound b hx

theorem integral_abs_tvHalfSecond_le {b : ℝ} (hb : 0 < b+1/2) :
    (∫ x : ℝ in Ioi 0, |tvHalfSecond b x|) ≤ 2*((|b|+1/2)^2+1/4)/(b+1/2) := by
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, (2*((|b|+1/2)^2+1/4))*Real.exp (-(b+1/2)*x) := by
      apply integral_mono_ae (integrableOn_tvHalfSecond hb).norm
        ((exp_neg_integrableOn_Ioi 0 hb).const_mul _)
      exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun x hx => by
        simpa only [Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using abs_tvHalfSecond_bound b hx.le))
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(b+1/2)<0)]
      simp only [mul_zero, Real.exp_zero]
      rw [div_neg, neg_div, neg_neg]
      ring

end UnitDistance.NumberFieldAnalysis
