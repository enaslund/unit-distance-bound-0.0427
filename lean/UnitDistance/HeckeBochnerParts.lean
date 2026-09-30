module

public import UnitDistance.HeckeBochnerReconstruction

@[expose] public section
set_option backward.privateInPublic true


open MeasureTheory Filter
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis

private theorem ofReal_abs_eq_parts (x : ℝ) :
    ENNReal.ofReal |x| = ENNReal.ofReal x + ENNReal.ofReal (-x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hx), add_zero]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', ENNReal.ofReal_eq_zero.mpr hx', zero_add]

variable {A B V : Type*} [MeasurableSpace A] [MeasurableSpace B] [Countable V]

theorem weighted_absolute_lower_mass_eq_add_parts
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    (w : A → ℝ) (f : V → A → B → ℝ)
    (hw : Measurable w) (hf : ∀ v, Measurable (fun p : A × B => f v p.1 p.2)) :
    (∫⁻ a, ENNReal.ofReal (w a) * (∫⁻ b, ∑' v, ENNReal.ofReal |f v a b| ∂ν) ∂μ) =
      (∫⁻ a, ENNReal.ofReal (w a) * (∫⁻ b, ∑' v, ENNReal.ofReal (f v a b) ∂ν) ∂μ) +
      (∫⁻ a, ENNReal.ofReal (w a) * (∫⁻ b, ∑' v, ENNReal.ofReal (-f v a b) ∂ν) ∂μ) := by
  have hpos : Measurable (fun p : A × B => ∑' v, ENNReal.ofReal (f v p.1 p.2)) :=
    Measurable.tsum (fun v => (hf v).ennreal_ofReal)
  have hpt (a : A) :
      ENNReal.ofReal (w a) * (∫⁻ b, ∑' v, ENNReal.ofReal |f v a b| ∂ν) =
      ENNReal.ofReal (w a) * (∫⁻ b, ∑' v, ENNReal.ofReal (f v a b) ∂ν) +
      ENNReal.ofReal (w a) * (∫⁻ b, ∑' v, ENNReal.ofReal (-f v a b) ∂ν) := by
    simp_rw [ofReal_abs_eq_parts, ENNReal.tsum_add]
    have hpa : Measurable (fun b : B => ∑' v, ENNReal.ofReal (f v a b)) :=
      hpos.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_add_left hpa]
    exact mul_add _ _ _
  rw [lintegral_congr hpt]
  exact lintegral_add_left (hw.ennreal_ofReal.mul hpos.lintegral_prod_right') _

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- Finite positive and negative masses alone suffice for the full signed Bochner reconstruction. -/
theorem weighted_iterated_tsum_reconstruction_of_parts
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (w : A → ℝ) (f : V → A → B → ℝ)
    (hw : Measurable w) (hwn : ∀ᵐ a ∂μ, 0 ≤ w a)
    (hf : ∀ v, Measurable (fun p : A × B => f v p.1 p.2))
    (hpos : (∫⁻ a, ENNReal.ofReal (w a) *
      (∫⁻ b, ∑' v, ENNReal.ofReal (f v a b) ∂ν) ∂μ) ≠ ⊤)
    (hneg : (∫⁻ a, ENNReal.ofReal (w a) *
      (∫⁻ b, ∑' v, ENNReal.ofReal (-f v a b) ∂ν) ∂μ) ≠ ⊤) :
    Integrable (fun a => w a * ∫ b, ∑' v, f v a b ∂ν) μ ∧
      (∫ a, w a * ∫ b, ∑' v, f v a b ∂ν ∂μ) =
        (∫⁻ a, ENNReal.ofReal (w a) *
          (∫⁻ b, ∑' v, ENNReal.ofReal (f v a b) ∂ν) ∂μ).toReal -
        (∫⁻ a, ENNReal.ofReal (w a) *
          (∫⁻ b, ∑' v, ENNReal.ofReal (-f v a b) ∂ν) ∂μ).toReal := by
  apply weighted_iterated_tsum_reconstruction μ ν w f hw hwn hf
  rw [weighted_absolute_lower_mass_eq_add_parts μ ν w f hw hf]
  exact ENNReal.add_ne_top.mpr ⟨hpos, hneg⟩

end UnitDistance.NumberFieldAnalysis
