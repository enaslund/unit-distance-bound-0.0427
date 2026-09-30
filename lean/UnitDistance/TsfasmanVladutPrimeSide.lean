module

public import UnitDistance.TsfasmanVladutRegularity
public import UnitDistance.Upstream.AINTLIB.ExplicitFormula.WeilAssembly

@[expose] public section
set_option backward.privateInPublic true


/-!
# Regularity of the actual prime side for the sech test function

Summable nonnegative weights preserve Lipschitz regularity under translates.
Applied to the actual prime-ideal Dirichlet weights, this supplies both
bounded variation and the two one-sided limits required by the Weil formula.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Topology NumberField
open scoped NNReal ENNReal
namespace UnitDistance.NumberFieldAnalysis

variable {ι : Type*}

theorem summable_weighted_translate {w shift : ι → ℝ} {G : ℝ → ℂ} {M : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (hG : ∀ x, ‖G x‖ ≤ M) (u : ℝ) :
    Summable (fun i => (w i : ℂ)*G (u+shift i)) := by
  apply Summable.of_norm_bounded (hs.mul_right M)
  intro i
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
  exact mul_le_mul_of_nonneg_left (hG _) (hw i)

theorem lipschitzWith_tsum_weighted_translate {w shift : ι → ℝ} {G : ℝ → ℂ}
    {C : ℝ≥0} {M : ℝ} (hw : ∀ i, 0 ≤ w i) (hs : Summable w)
    (hG : ∀ x, ‖G x‖ ≤ M) (hlip : LipschitzWith C G) :
    LipschitzWith (C * ⟨∑' i, w i, tsum_nonneg hw⟩)
      (fun u => ∑' i, (w i : ℂ)*G (u+shift i)) := by
  have hsum := summable_weighted_translate (shift := shift) hw hs hG
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← (hsum x).tsum_sub (hsum y)]
  calc
    ‖∑' i, ((w i : ℂ)*G (x+shift i)-(w i : ℂ)*G (y+shift i))‖
        ≤ ∑' i, ‖(w i : ℂ)*G (x+shift i)-(w i : ℂ)*G (y+shift i)‖ :=
      norm_tsum_le_tsum_norm ((hsum x).sub (hsum y)).norm
    _ ≤ ∑' i, w i * ((C:ℝ)*dist x y) := by
      apply Summable.tsum_le_tsum _ ((hsum x).sub (hsum y)).norm (hs.mul_right _)
      intro i
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw i), ← dist_eq_norm]
      apply mul_le_mul_of_nonneg_left _ (hw i)
      simpa only [dist_add_right] using hlip.dist_le_mul (x+shift i) (y+shift i)
    _ = (∑' i, w i)*((C:ℝ)*dist x y) := tsum_mul_right
    _ = ↑(C * ⟨∑' i, w i, tsum_nonneg hw⟩)*dist x y := by
      change (∑' i, w i)*((C:ℝ)*dist x y) = ((C:ℝ)*(∑' i, w i))*dist x y
      ring

variable (K : Type*) [Field K] [NumberField K]

abbrev tvPrimePowerIndex := {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} × ℕ

def tvPrimeSideWeight (a : ℝ) (pk : tvPrimePowerIndex K) : ℝ :=
  Real.log (Ideal.absNorm pk.1.1) *
    (Ideal.absNorm pk.1.1 : ℝ)^(-(((pk.2+1 : ℕ)):ℝ)*(1+a))

def tvPrimeSideShift (pk : tvPrimePowerIndex K) : ℝ :=
  (((pk.2+1 : ℕ)):ℝ)*Real.log (Ideal.absNorm pk.1.1)

theorem tvPrimeSideWeight_nonneg (a : ℝ) (pk : tvPrimePowerIndex K) :
    0 ≤ tvPrimeSideWeight K a pk := DedekindResidue.primeSideH_weight_nonneg K pk

theorem summable_tvPrimeSideWeight {a : ℝ} (ha : 0 < a) :
    Summable (tvPrimeSideWeight K a) :=
  DedekindResidue.summable_primeIdeal_pow_log_rpow K (by linarith : 1 < 1+a)

theorem primeSideH_tvKernel_eq (e a u : ℝ) :
    DedekindResidue.primeSideH K a (tvKernel e) u =
      ∑' pk, (tvPrimeSideWeight K a pk : ℂ) *
        tvWeighted e (1/2+a) (u+tvPrimeSideShift K pk) := rfl

theorem summable_primeSideH_tvKernel {e a : ℝ} (ha : 0 < a) (hae : a ≤ e) (u : ℝ) :
    Summable (fun pk => (tvPrimeSideWeight K a pk : ℂ) *
      tvWeighted e (1/2+a) (u+tvPrimeSideShift K pk)) := by
  apply summable_weighted_translate (tvPrimeSideWeight_nonneg K a)
    (summable_tvPrimeSideWeight K ha)
  exact norm_tvWeighted_le_two (by rw [abs_of_pos (by linarith : 0 < 1/2+a)]; linarith)

theorem lipschitzWith_primeSideH_tvKernel {e a : ℝ} (ha : 0 < a) (hae : a ≤ e) :
    LipschitzWith (tvLipschitzConstant e (1/2+a) *
      ⟨∑' pk, tvPrimeSideWeight K a pk, tsum_nonneg (tvPrimeSideWeight_nonneg K a)⟩)
      (DedekindResidue.primeSideH K a (tvKernel e)) := by
  have hc : |1/2+a| ≤ e+1/2 := by
    rw [abs_of_pos (by linarith : 0 < 1/2+a)]
    linarith
  change LipschitzWith _ (fun u => ∑' pk : tvPrimePowerIndex K,
    (tvPrimeSideWeight K a pk : ℂ)*tvWeighted e (1/2+a) (u+tvPrimeSideShift K pk))
  exact lipschitzWith_tsum_weighted_translate
    (w := tvPrimeSideWeight K a) (shift := tvPrimeSideShift K) (G := tvWeighted e (1/2+a))
    (tvPrimeSideWeight_nonneg K a)
    (summable_tvPrimeSideWeight K ha) (norm_tvWeighted_le_two hc)
    (lipschitzWith_tvWeighted hc)

theorem continuous_primeSideH_tvKernel {e a : ℝ} (ha : 0 < a) (hae : a ≤ e) :
    Continuous (DedekindResidue.primeSideH K a (tvKernel e)) :=
  (lipschitzWith_primeSideH_tvKernel K ha hae).continuous

theorem locallyBoundedVariationOn_primeSideH_tvKernel_re {e a : ℝ}
    (ha : 0 < a) (hae : a ≤ e) :
    LocallyBoundedVariationOn (fun u => (DedekindResidue.primeSideH K a (tvKernel e) u).re)
      univ :=
  (DedekindResidue.lipschitzWith_complex_re.comp
    (lipschitzWith_primeSideH_tvKernel K ha hae)).locallyBoundedVariationOn univ

theorem locallyBoundedVariationOn_primeSideH_tvKernel_im {e a : ℝ}
    (ha : 0 < a) (hae : a ≤ e) :
    LocallyBoundedVariationOn (fun u => (DedekindResidue.primeSideH K a (tvKernel e) u).im)
      univ :=
  (DedekindResidue.lipschitzWith_complex_im.comp
    (lipschitzWith_primeSideH_tvKernel K ha hae)).locallyBoundedVariationOn univ

end UnitDistance.NumberFieldAnalysis
