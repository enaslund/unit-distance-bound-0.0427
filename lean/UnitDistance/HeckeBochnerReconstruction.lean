module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section
set_option backward.privateInPublic true


/-! Bochner reconstruction from finite signed lower-integral masses. The
results retain the full countable series; absolute mass finiteness supplies
all almost-everywhere convergence and Fubini hypotheses. -/
open MeasureTheory Filter
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis

variable {A B V : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- A measurable countable real series with finite integrated absolute mass is
integrable, and its integral is the difference of the two lower-integral masses. -/
theorem integrable_tsum_and_integral_pos_sub_neg
    (μ : Measure A) [SFinite μ] (f : V → A → ℝ)
    (hf : ∀ v, Measurable (f v))
    (hfinite : (∫⁻ a, ∑' v, ENNReal.ofReal |f v a| ∂μ) ≠ ⊤) :
    Integrable (fun a => ∑' v, f v a) μ ∧
      (∫ a, ∑' v, f v a ∂μ) =
        (∫⁻ a, ∑' v, ENNReal.ofReal (f v a) ∂μ).toReal -
        (∫⁻ a, ∑' v, ENNReal.ofReal (-f v a) ∂μ).toReal := by
  let F : A × V → ℝ := fun p => f p.2 p.1
  have hF : Measurable F := measurable_from_prod_countable_left hf
  have hnorm : (∫⁻ p, ENNReal.ofReal ‖F p‖ ∂(μ.prod Measure.count)) =
      ∫⁻ a, ∑' v, ENNReal.ofReal |f v a| ∂μ := by
    rw [lintegral_prod _ hF.norm.ennreal_ofReal.aemeasurable]
    simp_rw [lintegral_count]
    simp only [F, Real.norm_eq_abs]
  have hFi : Integrable F (μ.prod Measure.count) :=
    ⟨hF.aestronglyMeasurable, (hasFiniteIntegral_iff_norm F).mpr
      (hnorm ▸ (lt_top_iff_ne_top.mpr hfinite))⟩
  have hsum : (fun a => ∫ v, F (a,v) ∂Measure.count) =ᵐ[μ] (fun a => ∑' v, f v a) := by
    filter_upwards [hFi.prod_right_ae] with a ha
    simpa only [F, count_real_singleton, one_smul] using integral_countable ha
  refine ⟨hFi.integral_prod_left.congr hsum, ?_⟩
  calc
    (∫ a, ∑' v, f v a ∂μ) = ∫ a, ∫ v, F (a,v) ∂Measure.count ∂μ :=
      integral_congr_ae hsum.symm
    _ = ∫ p, F p ∂(μ.prod Measure.count) := (integral_prod F hFi).symm
    _ = _ := by
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hFi]
      rw [lintegral_prod _ hF.ennreal_ofReal.aemeasurable,
        lintegral_prod (fun p : A × V => ENNReal.ofReal (-F p)) hF.neg.ennreal_ofReal.aemeasurable]
      simp_rw [lintegral_count]
      rfl

/-- Weighted iterated Bochner reconstruction. No pointwise convergence hypothesis
is needed: the finite total absolute mass supplies convergence almost everywhere. -/
theorem weighted_iterated_tsum_integral_pos_sub_neg
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (w : A → ℝ) (f : V → A → B → ℝ)
    (hw : Measurable w) (hf : ∀ v, Measurable (fun p : A × B => f v p.1 p.2))
    (hfinite : (∫⁻ a, ∫⁻ b, ∑' v, ENNReal.ofReal |w a * f v a b| ∂ν ∂μ) ≠ ⊤) :
    Integrable (fun a => w a * ∫ b, ∑' v, f v a b ∂ν) μ ∧
      (∫ a, w a * ∫ b, ∑' v, f v a b ∂ν ∂μ) =
        (∫⁻ a, ∫⁻ b, ∑' v, ENNReal.ofReal (w a * f v a b) ∂ν ∂μ).toReal -
        (∫⁻ a, ∫⁻ b, ∑' v, ENNReal.ofReal (-(w a * f v a b)) ∂ν ∂μ).toReal := by
  let G : V → A × B → ℝ := fun v p => w p.1 * f v p.1 p.2
  have hG (v : V) : Measurable (G v) := (hw.comp measurable_fst).mul (hf v)
  have hnorm : Measurable (fun p : A × B => ∑' v, ENNReal.ofReal |G v p|) :=
    by
    simpa only [Real.norm_eq_abs] using
      (Measurable.tsum (fun v => (hG v).norm.ennreal_ofReal))
  have hfin : (∫⁻ p, ∑' v, ENNReal.ofReal |G v p| ∂(μ.prod ν)) ≠ ⊤ := by
    rw [lintegral_prod _ hnorm.aemeasurable]
    exact hfinite
  obtain ⟨hint, heq⟩ := integrable_tsum_and_integral_pos_sub_neg (μ.prod ν) G hG hfin
  have hinner (a : A) : (∫ b, ∑' v, G v (a,b) ∂ν) = w a * ∫ b, ∑' v, f v a b ∂ν := by
    dsimp only [G]
    simp_rw [tsum_mul_left]
    rw [integral_const_mul]
  refine ⟨hint.integral_prod_left.congr (Eventually.of_forall hinner), ?_⟩
  calc
    _ = ∫ a, ∫ b, ∑' v, G v (a,b) ∂ν ∂μ := integral_congr_ae (Eventually.of_forall fun a => (hinner a).symm)
    _ = ∫ p, ∑' v, G v p ∂(μ.prod ν) := (integral_prod _ hint).symm
    _ = _ := heq
    _ = _ := by
      rw [lintegral_prod _ (Measurable.tsum (fun v => (hG v).ennreal_ofReal)).aemeasurable,
        lintegral_prod (fun p : A × B => ∑' v, ENNReal.ofReal (-G v p))
          (Measurable.tsum (fun v => (hG v).neg.ennreal_ofReal)).aemeasurable]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- A nonnegative outer weight can be moved through each signed lower mass. -/
theorem lower_mass_weight_outside
    (μ : Measure A) (ν : Measure B) (w : A → ℝ) (f : V → A → B → ℝ)
    (hw : ∀ᵐ a ∂μ, 0 ≤ w a) :
    (∫⁻ a, ∫⁻ b, ∑' v, ENNReal.ofReal (w a * f v a b) ∂ν ∂μ) =
      ∫⁻ a, ENNReal.ofReal (w a) * (∫⁻ b, ∑' v, ENNReal.ofReal (f v a b) ∂ν) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [hw] with a ha
  simp_rw [ENNReal.ofReal_mul ha, ENNReal.tsum_mul_left]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Direct form for the Mellin weight, with nonnegative weight outside the lower
integrals as in a Tonelli calculation. -/
theorem weighted_iterated_tsum_reconstruction
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (w : A → ℝ) (f : V → A → B → ℝ)
    (hw : Measurable w) (hwn : ∀ᵐ a ∂μ, 0 ≤ w a)
    (hf : ∀ v, Measurable (fun p : A × B => f v p.1 p.2))
    (hfinite : (∫⁻ a, ENNReal.ofReal (w a) *
      (∫⁻ b, ∑' v, ENNReal.ofReal |f v a b| ∂ν) ∂μ) ≠ ⊤) :
    Integrable (fun a => w a * ∫ b, ∑' v, f v a b ∂ν) μ ∧
      (∫ a, w a * ∫ b, ∑' v, f v a b ∂ν ∂μ) =
        (∫⁻ a, ENNReal.ofReal (w a) *
          (∫⁻ b, ∑' v, ENNReal.ofReal (f v a b) ∂ν) ∂μ).toReal -
        (∫⁻ a, ENNReal.ofReal (w a) *
          (∫⁻ b, ∑' v, ENNReal.ofReal (-f v a b) ∂ν) ∂μ).toReal := by
  have habs : (∫⁻ a, ∫⁻ b, ∑' v, ENNReal.ofReal |w a * f v a b| ∂ν ∂μ) =
      ∫⁻ a, ENNReal.ofReal (w a) * (∫⁻ b, ∑' v, ENNReal.ofReal |f v a b| ∂ν) ∂μ := by
    calc
      _ = ∫⁻ a, ∫⁻ b, ∑' v, ENNReal.ofReal (w a * |f v a b|) ∂ν ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hwn] with a ha
        simp only [abs_mul, abs_of_nonneg ha]
      _ = _ := lower_mass_weight_outside μ ν w (fun v a b => |f v a b|) hwn
  obtain ⟨hint, heq⟩ := weighted_iterated_tsum_integral_pos_sub_neg μ ν w f hw hf (habs ▸ hfinite)
  refine ⟨hint, ?_⟩
  rw [lower_mass_weight_outside μ ν w f hwn] at heq
  simp only [← mul_neg] at heq
  rw [lower_mass_weight_outside μ ν w (fun v a b => -f v a b) hwn] at heq
  exact heq

end UnitDistance.NumberFieldAnalysis
