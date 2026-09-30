module

public import UnitDistance.RelativeHeckeNormalization
public import UnitDistance.Upstream.AINTLIB.ExplicitFormula.ZeroCapture

@[expose] public section
set_option backward.privateInPublic true


/-! Ordinary consequences of an actual entire relative continuation.
The entire function is a factor of the ordinary pole-cleared completion;
no claim is made that the totalized raw quotient is entire at common zeros. -/
noncomputable section
open Filter Set Complex NumberField NumberField.InfinitePlace DedekindResidue
open scoped Topology
namespace UnitDistance.NumberFieldAnalysis
variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

/-- An entire relative factor inherits the actual functional equation. -/
theorem entireRelativeFactor_one_sub {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    (s : ℂ) : L (1-s) = L s := by
  have hleft : AnalyticOnNhd ℂ (fun z => L (1-z)) univ :=
    fun z _ => ((hL.comp ((differentiable_const (1:ℂ)).sub differentiable_id)).analyticAt z)
  have hright : AnalyticOnNhd ℂ L univ := fun z _ => hL.analyticAt z
  have hne : ∀ᶠ z in 𝓝 (1:ℂ), completedDedekindZetaEntire F z ≠ 0 :=
    (differentiable_completedDedekindZetaEntire F).continuous.continuousAt.eventually_ne
      (completedDedekindEntire_one_ne_zero F)
  have heq : (fun z => L (1-z)) =ᶠ[𝓝 (1:ℂ)] L := by
    filter_upwards [hne] with z hz
    apply mul_left_cancel₀ hz
    calc
      completedDedekindZetaEntire F z*L (1-z) =
          completedDedekindZetaEntire F (1-z)*L (1-z) := by rw [completedDedekindEntire_one_sub]
      _ = completedDedekindZetaEntire K (1-z) := (hfactor _).symm
      _ = completedDedekindZetaEntire K z := completedDedekindEntire_one_sub K z
      _ = completedDedekindZetaEntire F z*L z := hfactor z
  exact congrFun (hleft.eq_of_eventuallyEq hright heq) s

theorem entireRelativeFactor_eq_quotient {L : ℂ → ℂ}
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    {s : ℂ} (hs : completedDedekindZetaEntire F s ≠ 0) :
    L s = completedRelativeQuotient K F s := by
  rw [completedRelativeQuotient, hfactor, mul_div_cancel_left₀ _ hs]

theorem completedDedekindEntire_ne_zero_real {s : ℝ} (hs : 1 ≤ s) :
    completedDedekindZetaEntire F (s:ℂ) ≠ 0 := by
  rcases eq_or_lt_of_le hs with he | he
  · subst s
    exact completedDedekindEntire_one_ne_zero F
  · exact completedDedekindZetaEntire_ne_zero_of_one_lt_re F (by simpa using he)

theorem entireRelativeFactor_eq_relativeCompletedReal {L : ℂ → ℂ}
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    {ell s : ℝ} (hs : 1 ≤ s) (hreal : nrRealPlaces K = 0)
    (hcomplex : nrComplexPlaces K = nrRealPlaces F+2*nrComplexPlaces F)
    (hdiscr : Real.log |(discr K : ℝ)|-Real.log |(discr F : ℝ)| =
      (Module.finrank ℚ F : ℝ)*ell) :
    L (s:ℂ) = ((Real.exp (relativeCompletionLogScale F)*relativeCompletedReal K F ell s : ℝ):ℂ) := by
  rw [entireRelativeFactor_eq_quotient K F hfactor (completedDedekindEntire_ne_zero_real F hs)]
  exact completedRelativeQuotient_eq_relativeCompletedReal K F hs hreal hcomplex hdiscr

/-- Zeros of the relative factor are ordinary numerator zeros and lie in the critical strip. -/
theorem entireRelativeFactor_zero_strip {L : ℂ → ℂ}
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    {s : ℂ} (hs : L s = 0) : 0 ≤ s.re ∧ s.re ≤ 1 := by
  apply re_mem_of_completedDedekindZetaEntire_eq_zero K
  rw [hfactor, hs, mul_zero]

def centeredRelativeFactor (L : ℂ → ℂ) (z : ℂ) : ℂ := L (z+1/2)

theorem centeredRelativeFactor_differentiable {L : ℂ → ℂ} (hL : Differentiable ℂ L) :
    Differentiable ℂ (centeredRelativeFactor L) := by
  exact hL.comp (differentiable_id.add_const _)

theorem centeredRelativeFactor_neg {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    (z : ℂ) : centeredRelativeFactor L (-z) = centeredRelativeFactor L z := by
  unfold centeredRelativeFactor
  rw [show -z+(1:ℂ)/2 = 1-(z+1/2) by ring]
  exact entireRelativeFactor_one_sub K F hL hfactor _

theorem centeredRelativeFactor_zero_strip {L : ℂ → ℂ}
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    {z : ℂ} (hz : centeredRelativeFactor L z = 0) : |z.re| ≤ (1/2 : ℝ) := by
  have h := entireRelativeFactor_zero_strip K F hfactor hz
  change 0 ≤ (z+1/2).re ∧ (z+1/2).re ≤ 1 at h
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at h
  rw [abs_le]
  constructor <;> linarith

end UnitDistance.NumberFieldAnalysis
