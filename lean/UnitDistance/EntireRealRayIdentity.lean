module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Identity theorem from a real ray. The converging real sequence follows
Chris Birkbeck's AINTLIB Existence proof (2026, Apache-2.0); this generalization
applies to arbitrary entire functions, without Dirichlet-series analyticity. -/
noncomputable section
open Filter Set Complex
open scoped Topology
namespace UnitDistance.NumberFieldAnalysis

theorem frequently_eq_of_real_gt_one {f g : ℂ → ℂ}
    (h : ∀ x : ℝ, 1 < x → f (x:ℂ) = g (x:ℂ)) :
    ∃ᶠ z in 𝓝[≠] (2:ℂ), f z = g z := by
  have htend : Tendsto (fun n : ℕ => ((2+(1:ℝ)/(n+1):ℝ):ℂ)) atTop (𝓝[≠] (2:ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hre : Tendsto (fun n : ℕ => (2+(1:ℝ)/(n+1):ℝ)) atTop (𝓝 (2:ℝ)) := by
        simpa using Tendsto.const_add (2:ℝ) tendsto_one_div_add_atTop_nhds_zero_nat
      have hcomp := (Complex.continuous_ofReal.tendsto (2:ℝ)).comp hre
      refine hcomp.congr (fun n => rfl) |>.mono_right ?_
      rw [show ((2:ℝ):ℂ) = (2:ℂ) by norm_cast]
    · apply Eventually.of_forall
      intro n
      simp only [mem_compl_iff, mem_singleton_iff]
      intro he
      have he' : (2+(1:ℝ)/(n+1):ℝ) = 2 := by exact_mod_cast he
      have hp : (0:ℝ) < (1:ℝ)/(n+1) := by positivity
      linarith
  apply htend.frequently
  apply Frequently.of_forall
  intro n
  apply h
  have hp : (0:ℝ) < (1:ℝ)/(n+1) := by positivity
  linarith

/-- Agreement on the actual real ray globalizes to all complex arguments. -/
theorem entire_eq_of_real_gt_one {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ x : ℝ, 1 < x → f (x:ℂ) = g (x:ℂ)) : f = g :=
  (show AnalyticOnNhd ℂ f univ from fun z _ => hf.analyticAt z).eq_of_frequently_eq
    (show AnalyticOnNhd ℂ g univ from fun z _ => hg.analyticAt z)
    (frequently_eq_of_real_gt_one h)

end UnitDistance.NumberFieldAnalysis
