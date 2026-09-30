module

public import UnitDistance.RelativeHeckeCompletion

@[expose] public section
set_option backward.privateInPublic true


/-!
# Identifying the relative Hecke gamma factor

For the actual signatures and discriminants in a totally imaginary quadratic
extension, the quotient of ordinary completed zeta functions is a fixed
positive multiple of the manuscript's relative completion. The only premises
below are the displayed arithmetic equalities, with no analytic comparison
or continuation premise.
-/

noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue

namespace UnitDistance.NumberFieldAnalysis

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

theorem log_dedekindCompletionPrefactorReal {s : ℝ} (hs : 0 < s) :
    Real.log (dedekindCompletionPrefactorReal K s) =
      s/2 * Real.log (|(discr K : ℝ)|) +
      (nrRealPlaces K : ℝ) * (-(s/2)*Real.log Real.pi + Real.log (Real.Gamma (s/2))) +
      (nrComplexPlaces K : ℝ) *
        (Real.log 2 - s*Real.log (2*Real.pi) + Real.log (Real.Gamma s)) := by
  have hD : (0:ℝ) < |(discr K : ℝ)| := by
    exact_mod_cast abs_pos.mpr (discr_ne_zero K)
  have hG := Real.Gamma_pos_of_pos hs
  have hGh := Real.Gamma_pos_of_pos (half_pos hs)
  unfold dedekindCompletionPrefactorReal
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul (by positivity) hGh.ne',
    Real.log_mul (by positivity) hG.ne',
    Real.log_mul (by norm_num) (by positivity),
    Real.log_rpow hD, Real.log_rpow Real.pi_pos,
    Real.log_rpow (by positivity : (0:ℝ)<2*Real.pi)]
  ring

private theorem logGamma_duplication {s : ℝ} (hs : 0 < s) :
    Real.log (Real.Gamma (s/2)) + Real.log (Real.Gamma ((s+1)/2)) =
      Real.log (Real.Gamma s) + (1-s)*Real.log 2 + Real.log Real.pi/2 := by
  have hG := Real.Gamma_pos_of_pos hs
  have hGh := Real.Gamma_pos_of_pos (half_pos hs)
  have hGo := Real.Gamma_pos_of_pos (by linarith : (0:ℝ)<(s+1)/2)
  have h := congrArg Real.log (Real.Gamma_mul_Gamma_add_half (s/2))
  rw [show s/2+1/2 = (s+1)/2 by ring, show 2*(s/2) = s by ring,
    Real.log_mul hGh.ne' hGo.ne',
    Real.log_mul (by positivity) (Real.sqrt_pos.2 Real.pi_pos).ne',
    Real.log_mul hG.ne' (by positivity), Real.log_rpow (by norm_num),
    Real.log_sqrt Real.pi_pos.le] at h
  exact h

/-- The logarithm of the positive, argument-independent scalar suppressed in
manuscript equation `an:completion`. -/
def relativeCompletionLogScale : ℝ :=
  (nrComplexPlaces F : ℝ)*Real.log 2 - (nrRealPlaces F : ℝ)/2*Real.log Real.pi

theorem log_completionPrefactorRatio {ell s : ℝ} (hs : 0 < s)
    (hreal : nrRealPlaces K = 0)
    (hcomplex : nrComplexPlaces K = nrRealPlaces F + 2*nrComplexPlaces F)
    (hdiscr : Real.log |(discr K : ℝ)| - Real.log |(discr F : ℝ)| =
      (Module.finrank ℚ F : ℝ)*ell) :
    Real.log (dedekindCompletionPrefactorReal K s / dedekindCompletionPrefactorReal F s) =
      relativeGammaLog ell (nrRealPlaces F) (nrComplexPlaces F) s +
        relativeCompletionLogScale F := by
  rw [Real.log_div (dedekindCompletionPrefactorReal_pos K hs).ne'
    (dedekindCompletionPrefactorReal_pos F hs).ne',
    log_dedekindCompletionPrefactorReal K hs, log_dedekindCompletionPrefactorReal F hs,
    hreal, hcomplex]
  have hsig : (Module.finrank ℚ F : ℝ) =
      (nrRealPlaces F : ℝ)+2*(nrComplexPlaces F : ℝ) := by
    exact_mod_cast (card_add_two_mul_card_eq_rank F).symm
  rw [hsig] at hdiscr
  have hg := logGamma_duplication hs
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero]
  unfold relativeGammaLog relativeCompletionLogScale
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero]
  push_cast
  linear_combination (s/2)*hdiscr - (nrRealPlaces F : ℝ)*hg

theorem completionPrefactorRatio_eq {ell s : ℝ} (hs : 0 < s)
    (hreal : nrRealPlaces K = 0)
    (hcomplex : nrComplexPlaces K = nrRealPlaces F + 2*nrComplexPlaces F)
    (hdiscr : Real.log |(discr K : ℝ)| - Real.log |(discr F : ℝ)| =
      (Module.finrank ℚ F : ℝ)*ell) :
    dedekindCompletionPrefactorReal K s / dedekindCompletionPrefactorReal F s =
      Real.exp (relativeCompletionLogScale F) *
        Real.exp (relativeGammaLog ell (nrRealPlaces F) (nrComplexPlaces F) s) := by
  rw [← Real.exp_log (div_pos (dedekindCompletionPrefactorReal_pos K hs)
      (dedekindCompletionPrefactorReal_pos F hs)),
    log_completionPrefactorRatio K F hs hreal hcomplex hdiscr, Real.exp_add]
  ring

/-- Actual identification on the closed real comparison interval, including
the analytic value at one. -/
theorem completedRelativeQuotient_eq_relativeCompletedReal {ell s : ℝ} (hs : 1 ≤ s)
    (hreal : nrRealPlaces K = 0)
    (hcomplex : nrComplexPlaces K = nrRealPlaces F + 2*nrComplexPlaces F)
    (hdiscr : Real.log |(discr K : ℝ)| - Real.log |(discr F : ℝ)| =
      (Module.finrank ℚ F : ℝ)*ell) :
    completedRelativeQuotient K F (s:ℂ) =
      ((Real.exp (relativeCompletionLogScale F) * relativeCompletedReal K F ell s : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hs with hs₁ | hs₁
  · subst s
    rw [Complex.ofReal_one, completedRelativeQuotient_one,
      completionPrefactorRatio_eq K F (by norm_num : (0:ℝ)<1) hreal hcomplex hdiscr]
    simp only [relativeCompletedReal, relativeZetaReal]
    push_cast
    ring
  · rw [completedRelativeQuotient_eq_of_one_lt_re K F (by simpa using hs₁),
      completedZetaPrefactor_ofReal, completedZetaPrefactor_ofReal,
      ← Complex.ofReal_div,
      completionPrefactorRatio_eq K F (lt_trans zero_lt_one hs₁) hreal hcomplex hdiscr]
    have hz : relativeZeta K F (s:ℂ) = ((relativeZeta K F (s:ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [relativeZeta_im_eq_zero K F hs₁]
    rw [hz]
    simp only [relativeCompletedReal, relativeZetaReal, if_neg (ne_of_gt hs₁)]
    push_cast
    ring

end UnitDistance.NumberFieldAnalysis
