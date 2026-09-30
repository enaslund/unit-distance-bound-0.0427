module

public import UnitDistance.RelativeZeroDivisor
public import UnitDistance.EntireFactorHadamard
public import UnitDistance.DedekindZetaGrowth
public import UnitDistance.RelativeHeckeComparison

@[expose] public section
set_option backward.privateInPublic true


/-! An actual entire relative factor suffices for the Hecke comparison.
Divisor, inverse-square summability, evenness, strip bounds and all growth
estimates are derived here from the ordinary completed Dedekind zeta functions. -/
noncomputable section
open Filter Set Complex NumberField NumberField.InfinitePlace DedekindResidue
open scoped Topology
namespace UnitDistance.NumberFieldAnalysis
open UnitDistance.EntireDivisor OverflowResidueRH
variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

theorem centeredRelativeFactor_norm_monotone {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s) :
    MonotoneOn (fun t : ℝ => ‖centeredRelativeFactor L (t:ℂ)‖) (Ici (1/2:ℝ)) := by
  let E := relativeEntireEvenFunction K F hL hfactor
  let N : ℂ → ℂ := fun z => completedDedekindZetaEntire K (z+1/2)
  let D : ℂ → ℂ := fun z => completedDedekindZetaEntire F (z+1/2)
  have hN : Differentiable ℂ N := (differentiable_completedDedekindZetaEntire K).comp
    (differentiable_id.add_const _)
  have hD : Differentiable ℂ D := (differentiable_completedDedekindZetaEntire F).comp
    (differentiable_id.add_const _)
  have hNfinite : ∀ z, analyticOrderAt N z ≠ ⊤ := by
    intro z
    have horder := analyticOrderAt_comp_of_deriv_ne_zero
      (f := completedDedekindZetaEntire K) (g := fun w : ℂ => w+1/2)
      (z₀ := z) (by fun_prop) (by simp)
    rw [show analyticOrderAt N z = analyticOrderAt (completedDedekindZetaEntire K) (z+1/2)
      from horder]
    exact completedZeta_analyticOrder_finite K _
  have hDne : ∃ z, D z ≠ 0 := by
    refine ⟨1/2, ?_⟩
    norm_num [D]
    exact completedDedekindEntire_one_ne_zero F
  have hNg := HeckeAnalysis.subquadraticLogNormGrowth_translate
    (completedDedekindZetaEntire_subquadratic_log_norm_growth K) (1/2 : ℂ)
  have hDg := HeckeAnalysis.subquadraticLogNormGrowth_translate
    (completedDedekindZetaEntire_subquadratic_log_norm_growth F) (1/2 : ℂ)
  apply HeckeAnalysis.norm_monotoneOn_of_entire_factor hN hD E.differentiable
    (fun z => hfactor (z+1/2)) hDne hNfinite hNg hDg
    (relativeZeroOccurrence_invSqSummability K F hL hfactor)
    (ZeroOccurrenceNormProper E) (ZeroOccurrenceNegationPairingData E) (OriginMultiplicity E)
    (analyticOrderAt_eq_canonical_divisor E) E.even (by norm_num)
  intro i
  exact centeredRelativeFactor_zero_strip K F hfactor (ZeroOccurrenceLoc_is_zero E i)

theorem relativeCompletedReal_monotoneOn_of_entire_factor {L : ℂ → ℂ}
    (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    {ell : ℝ} (hreal : nrRealPlaces K = 0)
    (hcomplex : nrComplexPlaces K = nrRealPlaces F+2*nrComplexPlaces F)
    (hdiscr : Real.log |(discr K : ℝ)|-Real.log |(discr F : ℝ)| =
      (Module.finrank ℚ F : ℝ)*ell) :
    MonotoneOn (relativeCompletedReal K F ell) (Ici 1) := by
  have heq : ∀ s : ℝ, 1 ≤ s →
      ‖centeredRelativeFactor L ((s-1/2:ℝ):ℂ)‖ =
        Real.exp (relativeCompletionLogScale F)*relativeCompletedReal K F ell s := by
    intro s hs
    unfold centeredRelativeFactor
    rw [show ((s-1/2:ℝ):ℂ)+(1:ℂ)/2 = (s:ℂ) by push_cast; ring,
      entireRelativeFactor_eq_relativeCompletedReal K F hfactor hs hreal hcomplex hdiscr,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (Real.exp_pos _) (relativeCompletedReal_pos K F ell hs))]
  intro s hs t ht hst
  have h := centeredRelativeFactor_norm_monotone K F hL hfactor
    (a := s-1/2) (b := t-1/2) (by change 1/2 ≤ s-1/2; change 1 ≤ s at hs; linarith)
    (by change 1/2 ≤ t-1/2; change 1 ≤ t at ht; linarith) (by linarith)
  dsimp only at h
  rw [heq s hs, heq t ht] at h
  exact le_of_mul_le_mul_left h (Real.exp_pos _)

variable [Algebra F K]

theorem normalized_log_relativeResidue_le_of_entire_factor
    (hdegree : Module.finrank F K = 2) {L : ℂ → ℂ}
    (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    {ell : ℝ} (hreal : nrRealPlaces K = 0)
    (hcomplex : nrComplexPlaces K = nrRealPlaces F+2*nrComplexPlaces F)
    (hdiscr : Real.log |(discr K : ℝ)|-Real.log |(discr F : ℝ)| =
      (Module.finrank ℚ F : ℝ)*ell)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Real.log (relativeResidue K F)/(Module.finrank ℚ F : ℝ) ≤
      Real.log (dedekindZeta K (1+epsilon)).re/(2*(Module.finrank ℚ F : ℝ)) +
        relativeGammaCorrection ell epsilon
          ((nrComplexPlaces F : ℝ)/(Module.finrank ℚ F : ℝ)) := by
  apply normalized_log_relativeResidue_le_zeta_of_completion_le K F hdegree ell hepsilon
  exact relativeCompletedReal_monotoneOn_of_entire_factor K F hL hfactor hreal hcomplex hdiscr
    (by simp) (by change 1 ≤ 1+epsilon; linarith) (by linarith)

end UnitDistance.NumberFieldAnalysis
