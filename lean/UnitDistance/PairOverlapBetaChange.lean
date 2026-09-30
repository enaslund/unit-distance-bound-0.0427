module

public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Positive-quadrant changes of variables for the overlap Laplace integral.
The nonnegative formulation supplies Tonelli without prior finiteness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal
namespace UnitDistance

/-- The additive shear converts the positive quadrant to a triangle. -/
theorem lintegral_positiveQuadrant_eq_triangle
    (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ r in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), f (r, t)) =
      ∫⁻ u in Ioi (0 : ℝ), ∫⁻ t in Ioo (0 : ℝ) u, f (u - t, t) := by
  let T : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 < p.1}
  have hT : MeasurableSet T := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hpre : (fun p : ℝ × ℝ => (p.1 - p.2, p.2)) ⁻¹'
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) = T := by
    ext p
    simp only [mem_preimage, mem_prod, mem_Ioi, T, mem_setOf_eq, sub_pos]
    exact and_comm
  have h := (measurePreserving_sub_prod (volume : Measure ℝ) volume).setLIntegral_comp_preimage
    (s := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (measurableSet_Ioi.prod measurableSet_Ioi) hf
  rw [hpre, ← Measure.prod_restrict, lintegral_prod f hf.aemeasurable] at h
  have hF : Measurable (fun p : ℝ × ℝ => f (p.1 - p.2, p.2)) :=
    hf.comp ((measurable_fst.sub measurable_snd).prodMk measurable_snd)
  rw [← lintegral_indicator hT, lintegral_prod _ (hF.indicator hT).aemeasurable] at h
  rw [← h, ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro u
  by_cases hu : 0 < u
  · rw [indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu),
      ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro t
    simp only [indicator_apply, T, mem_setOf_eq, mem_Ioo]
  · rw [indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards with t
    apply indicator_of_notMem
    change ¬ (0 < t ∧ t < u)
    intro ht
    exact hu (lt_trans ht.1 ht.2)

/-- Scaling a positive interval, with its exact Jacobian. -/
theorem lintegral_Ioo_scale (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    {u : ℝ} (hu : 0 < u) :
    (∫⁻ t in Ioo (0 : ℝ) u, f t) =
      ENNReal.ofReal u * ∫⁻ v in Ioo (0 : ℝ) 1, f (u * v) := by
  have hpre : (fun v : ℝ => u * v) ⁻¹' Ioo (0 : ℝ) u = Ioo (0 : ℝ) 1 := by
    ext v
    simp only [mem_preimage, mem_Ioo]
    constructor
    · intro h
      constructor
      · exact (mul_pos_iff_of_pos_left hu).mp h.1
      · exact (mul_lt_mul_iff_right₀ hu).mp (by simpa using h.2)
    · intro h
      constructor
      · exact mul_pos hu h.1
      · simpa using (mul_lt_mul_iff_right₀ hu).mpr h.2
  conv_lhs => rw [← Real.smul_map_volume_mul_left hu.ne']
  rw [Measure.restrict_smul, lintegral_smul_measure, abs_of_pos hu,
    setLIntegral_map measurableSet_Ioo hf (measurable_const_mul u), hpre]
  rfl

/-- Feynman parameters on the positive quadrant, valid for every measurable
nonnegative kernel. -/
theorem lintegral_positiveQuadrant_eq_betaParameters
    (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ r in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), f (r, t)) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u *
        ∫⁻ v in Ioo (0 : ℝ) 1, f (u * (1 - v), u * v) := by
  rw [lintegral_positiveQuadrant_eq_triangle f hf]
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  rw [lintegral_Ioo_scale (fun t => f (u - t, t))
    (hf.comp ((measurable_const.sub measurable_id).prodMk measurable_id)) hu]
  congr 1
  apply lintegral_congr
  intro v
  congr 1
  ext <;> dsimp <;> ring

/-- The same parameterization with the first coordinate `u*v`. -/
theorem lintegral_positiveQuadrant_eq_betaParameters_first
    (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ r in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), f (r, t)) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u *
        ∫⁻ v in Ioo (0 : ℝ) 1, f (u * v, u * (1 - v)) := by
  have hs := lintegral_lintegral_swap (f := fun r t => f (r, t))
    (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioi (0 : ℝ)))
    hf.aemeasurable
  rw [hs]
  exact lintegral_positiveQuadrant_eq_betaParameters (fun p => f (p.2, p.1))
    (hf.comp (measurable_snd.prodMk measurable_fst))

end UnitDistance
