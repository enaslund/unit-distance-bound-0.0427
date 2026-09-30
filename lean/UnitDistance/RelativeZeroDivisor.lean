module

public import UnitDistance.CanonicalEntireDivisor
public import UnitDistance.RelativeEntireContinuation
public import UnitDistance.Upstream.AINTLIB.ExplicitFormula.ZeroSummability

@[expose] public section
set_option backward.privateInPublic true


/-! Actual multiplicities of a relative entire factor are bounded by the
ordinary numerator divisor, giving summability without a zero-count premise. -/
noncomputable section
open Filter Set Complex NumberField DedekindResidue
open scoped Topology BigOperators
namespace UnitDistance.NumberFieldAnalysis
open UnitDistance.EntireDivisor OverflowResidueRH
variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

theorem completedZeta_analyticOrder_finite (s : ℂ) :
    analyticOrderAt (completedDedekindZetaEntire K) s ≠ ⊤ := by
  intro h
  apply meromorphicOrderAt_completedDedekindZetaEntire_ne_top K s
  rw [(analyticAt_completedDedekindZetaEntire K s).meromorphicOrderAt_eq, h]
  rfl

theorem zetaZeroDivisor_eq_natOrder (s : ℂ) :
    zetaZeroDivisor K s = (analyticOrderNatAt (completedDedekindZetaEntire K) s : ℤ) := by
  rw [zetaZeroDivisor, MeromorphicOn.divisor_apply
    (fun z _ => (analyticAt_completedDedekindZetaEntire K z).meromorphicAt) (mem_univ s),
    (analyticAt_completedDedekindZetaEntire K s).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (completedZeta_analyticOrder_finite K s)]
  simp

def relativeEntireEvenFunction {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s) :
    EntireEvenFunction where
  toFun := centeredRelativeFactor L
  differentiable := centeredRelativeFactor_differentiable hL
  nontrivial := by
    refine ⟨1/2, ?_⟩
    intro h
    have hone : L 1 = 0 := by
      norm_num [centeredRelativeFactor] at h
      exact h
    apply completedDedekindEntire_one_ne_zero K
    rw [hfactor, hone, mul_zero]
  even := centeredRelativeFactor_neg K F hL hfactor

theorem centeredRelativeFactor_analyticOrder {L : ℂ → ℂ} (z : ℂ) :
    analyticOrderAt (centeredRelativeFactor L) z = analyticOrderAt L (z+1/2) := by
  exact analyticOrderAt_comp_of_deriv_ne_zero (f := L) (g := fun w : ℂ => w+1/2)
    (z₀ := z) (by fun_prop) (by simp)

theorem relativeZeroMultiplicity_le {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    (z : ℂ) :
    (analyticOrderNatAt (centeredRelativeFactor L) z : ℝ) ≤
      (zetaZeroDivisor K (z+1/2) : ℝ) := by
  have h : analyticOrderAt L (z+1/2) ≤
      analyticOrderAt (completedDedekindZetaEntire K) (z+1/2) := by
    rw [show completedDedekindZetaEntire K = completedDedekindZetaEntire F*L from funext hfactor,
      analyticOrderAt_mul (analyticAt_completedDedekindZetaEntire F _) (hL.analyticAt _)]
    exact le_add_self
  have hn := ENat.toNat_le_toNat h (completedZeta_analyticOrder_finite K _)
  rw [zetaZeroDivisor_eq_natOrder]
  simp only [analyticOrderNatAt, centeredRelativeFactor_analyticOrder]
  exact_mod_cast hn

def relativeZeroPointToZeta {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    (z : NonzeroZero (relativeEntireEvenFunction K F hL hfactor)) : ZetaZeros K :=
  ⟨z.1+1/2, (zetaZeroDivisor_ne_zero_iff K).mpr (by
    rw [hfactor]
    exact mul_eq_zero.mpr (Or.inr z.2.1))⟩

theorem relativeZeroPointToZeta_injective {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s) :
    Function.Injective (relativeZeroPointToZeta K F hL hfactor) := by
  intro z w h
  apply Subtype.ext
  exact add_right_cancel (congrArg Subtype.val h)

theorem summable_relativeZeroPoint_weights {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s) :
    Summable (fun z : NonzeroZero (relativeEntireEvenFunction K F hL hfactor) =>
      (analyticOrderNatAt (centeredRelativeFactor L) z.1 : ℝ)/(1+z.1.im^2)) := by
  have hs := (summable_zetaZeros_inv_sq K 1 (by norm_num)).comp_injective
    (relativeZeroPointToZeta_injective K F hL hfactor)
  have hs' : Summable (fun z : NonzeroZero (relativeEntireEvenFunction K F hL hfactor) =>
      (zetaZeroDivisor K (z.1+1/2) : ℝ)/(1+z.1.im^2)) := by
    simpa [Function.comp_def, relativeZeroPointToZeta] using hs
  apply hs'.of_nonneg_of_le
  · intro z
    positivity
  · intro z
    exact div_le_div_of_nonneg_right (relativeZeroMultiplicity_le K F hL hfactor z.1)
      (by positivity)

theorem summable_relativeZeroOccurrence_weights {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s) :
    Summable (fun i : ZeroOccurrence (relativeEntireEvenFunction K F hL hfactor) =>
      1/(1+(ZeroOccurrenceLoc _ i).im^2)) := by
  rw [show (fun i : ZeroOccurrence (relativeEntireEvenFunction K F hL hfactor) =>
      1/(1+(ZeroOccurrenceLoc _ i).im^2)) =
    (fun i : (Σ z : NonzeroZero (relativeEntireEvenFunction K F hL hfactor),
      Fin (analyticOrderNatAt (centeredRelativeFactor L) z.1)) =>
      1/(1+i.1.1.im^2)) from rfl]
  apply (summable_sigma_of_nonneg (fun i => by positivity)).mpr
  refine ⟨fun _ => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
  simpa [tsum_fintype, nsmul_eq_mul, div_eq_mul_inv] using
    summable_relativeZeroPoint_weights K F hL hfactor

theorem summable_inv_sq_of_im_weight {ι : Type*} {zeros : ι → ℂ}
    (hproper : HadamardZeroNormProper zeros)
    (hs : Summable (fun i => 1/(1+(zeros i).im^2))) :
    Summable (fun i => (‖zeros i‖^2)⁻¹) := by
  apply (hs.mul_left 2).of_norm_bounded_eventually
  have hlarge : ∀ᶠ i in cofinite, 1 ≤ ‖zeros i‖ := by
    simpa using hproper.eventually_large (1/2 : ℂ)
  filter_upwards [hlarge] with i hi
  have hn : 0 < ‖zeros i‖^2 := by positivity
  have hd : 0 < 1+(zeros i).im^2 := by positivity
  have him : (zeros i).im^2 ≤ ‖zeros i‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [sq_nonneg (zeros i).re]
  have hden : 1+(zeros i).im^2 ≤ 2*‖zeros i‖^2 := by nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), ← one_div]
  rw [← mul_div_assoc, mul_one]
  exact (div_le_div_iff₀ hn hd).mpr (by simpa using hden)

theorem relativeZeroOccurrence_invSqSummability {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s) :
    HadamardZeroInvSqSummability
      (ZeroOccurrenceLoc (relativeEntireEvenFunction K F hL hfactor)) := by
  apply HadamardZeroInvSqSummability.of_invSqSummable_normProper
    (ZeroOccurrenceLoc_ne_zero _) _ (ZeroOccurrenceNormProper _)
  exact summable_inv_sq_of_im_weight (ZeroOccurrenceNormProper _)
    (summable_relativeZeroOccurrence_weights K F hL hfactor)

end UnitDistance.NumberFieldAnalysis
