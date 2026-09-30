module

public import UnitDistance.RelativeHeckeDiscriminant
public import UnitDistance.RelativeClassNumber
public import UnitDistance.TsfasmanVladutPrimeLimits

@[expose] public section
set_option backward.privateInPublic true


/-! A right-half-plane formulation of actual relative entire continuation,
using only ordinary Dedekind zeta and the explicit Gamma/discriminant factors.
The identity theorem supplies the canonical completed entire factor. -/
noncomputable section
open Filter Set Complex NumberField NumberField.InfinitePlace DedekindResidue
open scoped Topology
namespace UnitDistance.NumberFieldAnalysis

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

/-- The ordinary completed zeta expression in its half-plane of absolute
convergence. The definition itself uses only Mathlib quantities. -/
def completedZetaRight (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| : ℝ) : ℂ)^(s/2) *
    (Complex.Gammaℝ s^nrRealPlaces K * Complex.Gammaℂ s^nrComplexPlaces K) *
      dedekindZeta K s

/-- The identity theorem makes the explicit right-half-plane factorization
an actual factorization of the canonical completed entire functions. -/
theorem entireFactor_of_rightHalfPlane {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s : ℂ, 1 < s.re → completedZetaRight K s = completedZetaRight F s*L s) :
    ∀ s : ℂ, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s := by
  have hleft : AnalyticOnNhd ℂ (completedDedekindZetaEntire K) univ :=
    fun s _ => (differentiable_completedDedekindZetaEntire K).analyticAt s
  have hright : AnalyticOnNhd ℂ (fun s => completedDedekindZetaEntire F s*L s) univ :=
    fun s _ => ((differentiable_completedDedekindZetaEntire F).mul hL).analyticAt s
  have heq : completedDedekindZetaEntire K =ᶠ[𝓝 (2:ℂ)]
      fun s => completedDedekindZetaEntire F s*L s := by
    have hregion : ∀ᶠ s : ℂ in 𝓝 2, 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hregion] with s hs
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    rw [completedDedekindZetaEntire_eq K hs0 hs1,
      completedDedekindZetaEntire_eq F hs0 hs1,
      completedDedekindZeta_eq_of_one_lt_re K hs,
      completedDedekindZeta_eq_of_one_lt_re F hs]
    have he : completedZetaPrefactor K s*dedekindZeta K s =
        completedZetaPrefactor F s*dedekindZeta F s*L s := hfactor s hs
    rw [he]
    ring
  exact fun s => congrFun (hleft.eq_of_eventuallyEq hright heq) s

variable [Algebra F K] [IsTotallyComplex K]

/-- Actual unramified quadratic data discharge the signature and
log-discriminant-ratio obligations in the entire-factor comparison. -/
theorem relativeCompletedReal_monotoneOn_of_unramified_entire_factor
    (hquad : Module.finrank F K = 2) (hunr : FiniteUnramified F K)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s : ℂ, 1 < s.re → completedZetaRight K s = completedZetaRight F s*L s)
    {ell : ℝ} (hdisc : Real.log (rootDiscriminant F) ≤ ell) :
    MonotoneOn (relativeCompletedReal K F ell) (Ici 1) := by
  apply relativeCompletedReal_monotoneOn_of_entire_factor_discr_le K F hL
    (entireFactor_of_rightHalfPlane K F hL hfactor)
    (IsTotallyComplex.nrRealPlaces_eq_zero K)
  · rw [nrComplexPlaces_eq_base_degree K F hquad]
    exact (card_add_two_mul_card_eq_rank F).symm
  · have hD := absoluteDiscriminant_eq_pow_of_finiteUnramified F K hunr
    rw [hquad] at hD
    have hlog : Real.log |(discr K : ℝ)| = 2*Real.log |(discr F : ℝ)| := by
      rw [← absoluteDiscriminant_eq_abs K, hD, Real.log_pow,
        absoluteDiscriminant_eq_abs F]
      norm_num
    rw [hlog]
    rw [tv_log_rootDiscriminant, absoluteDiscriminant_eq_abs] at hdisc
    have hd : (0:ℝ) < Module.finrank ℚ F := by
      exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=F)
    have h := (div_le_iff₀ hd).mp hdisc
    nlinarith

end UnitDistance.NumberFieldAnalysis
