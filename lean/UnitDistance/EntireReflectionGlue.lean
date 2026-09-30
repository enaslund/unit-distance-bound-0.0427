module

public import UnitDistance.RelativeEntireContinuation

@[expose] public section
set_option backward.privateInPublic true


/-! Removing a finite Euler denominator by reflection. An entire imprimitive
factor with denominator zeros only on Re(s)=0 gives an entire primitive factor,
using the actual numerator and denominator functional equations. -/
noncomputable section
open Filter Set Complex
open scoped Topology
namespace UnitDistance.HeckeAnalysis

def reflectedQuotient (E D : ℂ → ℂ) (s : ℂ) : ℂ :=
  if 0 < s.re then E s/D s else E (1-s)/D (1-s)

theorem exists_entire_factor_of_imprimitive
    {N G E D : ℂ → ℂ}
    (hN : Differentiable ℂ N) (hG : Differentiable ℂ G)
    (hE : Differentiable ℂ E) (hD : Differentiable ℂ D)
    (hNfe : ∀ s, N (1-s) = N s) (hGfe : ∀ s, G (1-s) = G s)
    (hGne : G 1 ≠ 0) (hDne : ∀ s : ℂ, s.re ≠ 0 → D s ≠ 0)
    (hprod : ∀ s : ℂ, 1 < s.re → N s*D s = G s*E s) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ ∀ s, N s = G s*L s := by
  have hglobal : ∀ s, N s*D s = G s*E s := by
    have hnear : ∀ᶠ s in 𝓝 (2:ℂ), 1 < s.re :=
      continuous_re.continuousAt.tendsto.eventually_const_lt (by norm_num)
    have hl : AnalyticOnNhd ℂ (fun s => N s*D s) univ := fun s _ => (hN.mul hD).analyticAt s
    have hr : AnalyticOnNhd ℂ (fun s => G s*E s) univ := fun s _ => (hG.mul hE).analyticAt s
    have heq : (fun s => N s*D s) =ᶠ[𝓝 (2:ℂ)] (fun s => G s*E s) := by
      filter_upwards [hnear] with s hs
      exact hprod s hs
    exact fun s => congrFun (hl.eq_of_eventuallyEq hr heq) s
  have hcross : ∀ s, E s*D (1-s) = E (1-s)*D s := by
    have hnear : ∀ᶠ s in 𝓝 (1:ℂ), G s ≠ 0 := hG.continuous.continuousAt.eventually_ne hGne
    have hl : AnalyticOnNhd ℂ (fun s => E s*D (1-s)) univ := by
      intro s _
      exact (hE.mul (hD.comp ((differentiable_const (1:ℂ)).sub differentiable_id))).analyticAt s
    have hr : AnalyticOnNhd ℂ (fun s => E (1-s)*D s) univ := by
      intro s _
      exact ((hE.comp ((differentiable_const (1:ℂ)).sub differentiable_id)).mul hD).analyticAt s
    have heq : (fun s => E s*D (1-s)) =ᶠ[𝓝 (1:ℂ)] (fun s => E (1-s)*D s) := by
      filter_upwards [hnear] with s hs
      apply mul_left_cancel₀ hs
      have href := hglobal (1-s)
      rw [hNfe, hGfe] at href
      calc
        G s*(E s*D (1-s)) = (G s*E s)*D (1-s) := by ring
        _ = (N s*D s)*D (1-s) := by rw [hglobal]
        _ = (N s*D (1-s))*D s := by ring
        _ = (G s*E (1-s))*D s := by rw [href]
        _ = G s*(E (1-s)*D s) := by ring
    exact fun s => congrFun (hl.eq_of_eventuallyEq hr heq) s
  have hright : ∀ s : ℂ, 0 < s.re → reflectedQuotient E D s = E s/D s := by
    intro s hs
    simp only [reflectedQuotient, if_pos hs]
  have hleft : ∀ s : ℂ, s.re < 1 → reflectedQuotient E D s = E (1-s)/D (1-s) := by
    intro s hs
    by_cases hp : 0 < s.re
    · rw [hright s hp]
      apply (div_eq_div_iff (hDne s hp.ne') (hDne (1-s) ?_)).mpr (hcross s)
      simp only [sub_re, one_re]
      linarith
    · simp only [reflectedQuotient, if_neg hp]
  refine ⟨reflectedQuotient E D, ?_, ?_⟩
  · intro s
    by_cases hp : 0 < s.re
    · have hnear : ∀ᶠ z in 𝓝 s, 0 < z.re :=
        continuous_re.continuousAt.tendsto.eventually_const_lt hp
      have ha : AnalyticAt ℂ (fun z => E z/D z) s :=
        (hE.analyticAt s).div (hD.analyticAt s) (hDne s hp.ne')
      apply AnalyticAt.differentiableAt
      apply ha.congr
      filter_upwards [hnear] with z hz
      exact (hright z hz).symm
    · have hs : s.re < 1 := by linarith
      have hnear : ∀ᶠ z in 𝓝 s, z.re < 1 :=
        continuous_re.continuousAt.tendsto.eventually_lt_const hs
      have hDr : D (1-s) ≠ 0 := hDne (1-s) (by simp only [sub_re, one_re]; linarith)
      have ha : AnalyticAt ℂ (fun z => E (1-z)/D (1-z)) s :=
        ((hE.comp ((differentiable_const (1:ℂ)).sub differentiable_id)).analyticAt s).div
          ((hD.comp ((differentiable_const (1:ℂ)).sub differentiable_id)).analyticAt s) hDr
      apply AnalyticAt.differentiableAt
      apply ha.congr
      filter_upwards [hnear] with z hz
      exact (hleft z hz).symm
  · intro s
    by_cases hp : 0 < s.re
    · rw [hright s hp, ← mul_div_assoc]
      exact (eq_div_iff (hDne s hp.ne')).mpr (hglobal s)
    · have hs : s.re < 1 := by linarith
      rw [hleft s hs, ← hNfe s, ← hGfe s, ← mul_div_assoc]
      exact (eq_div_iff (hDne (1-s) (by simp only [sub_re, one_re]; linarith))).mpr (hglobal (1-s))

end UnitDistance.HeckeAnalysis
