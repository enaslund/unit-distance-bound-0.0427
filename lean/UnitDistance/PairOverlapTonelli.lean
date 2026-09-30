module

public import UnitDistance.PairOverlapExpansion

@[expose] public section
set_option backward.privateInPublic true


/-!
# Tonelli reduction of one Student convolution

This is the measure-theoretic core of the overlap certificate.  It replaces
two Student factors by their positive Laplace kernels and changes the order
of the spatial and Laplace integrations.  The statement is in `ℝ≥0∞`, so
Tonelli applies before any finiteness argument.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnitDistance.Witness

def pairOverlapLaplaceAt (α : ℝ) (z : ℂ) (r : ℝ) : ℝ :=
  pairOverlapLaplaceKernel α (a * ‖z‖ ^ 2) r

theorem pairOverlapLaplaceAt_nonneg {α r : ℝ} {z : ℂ} (hr : 0 ≤ r) :
    0 ≤ pairOverlapLaplaceAt α z r :=
  pairOverlapLaplaceKernel_nonneg hr

theorem measurable_pairOverlapLaplaceAt (α : ℝ) :
    Measurable (Function.uncurry (fun z : ℂ => pairOverlapLaplaceAt α z)) := by
  unfold pairOverlapLaplaceAt pairOverlapLaplaceKernel
  fun_prop

theorem integrableOn_pairOverlapLaplaceAt {α : ℝ} (hα : 0 < α) (z : ℂ) :
    IntegrableOn (pairOverlapLaplaceAt α z) (Ioi 0) := by
  have hG := Real.GammaIntegral_convergent hα
  apply hG.mono'
  · exact ((measurable_pairOverlapLaplaceAt α).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    unfold pairOverlapLaplaceAt pairOverlapLaplaceKernel
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _)
      (Real.exp_pos _).le)]
    have hx : 0 ≤ a * ‖z‖ ^ 2 := mul_nonneg witness_basic.2.1.le (sq_nonneg _)
    have he : Real.exp (-(r * (1 + a * ‖z‖ ^ 2))) ≤ Real.exp (-r) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hr.le hx]
    have hp : 0 ≤ r ^ (α - 1) := Real.rpow_nonneg hr.le _
    calc
      r ^ (α - 1) * Real.exp (-(r * (1 + a * ‖z‖ ^ 2))) ≤
          r ^ (α - 1) * Real.exp (-r) := mul_le_mul_of_nonneg_left he hp
      _ = Real.exp (-r) * r ^ (α - 1) := mul_comm _ _

private theorem studentCoordinate_rpow_eq (α : ℝ) (z : ℂ) :
    studentCoordinate z ^ α = (1 + a * ‖z‖ ^ 2) ^ (-α) := by
  have hb : 0 ≤ 1 + a * ‖z‖ ^ 2 := by positivity [witness_basic.2.1]
  unfold studentCoordinate
  rw [Real.inv_rpow hb, Real.rpow_neg hb]

private theorem measurable_studentCoordinate : Measurable studentCoordinate := by
  unfold studentCoordinate
  fun_prop

/-- The normalized pointwise Laplace representation in a form usable by
Tonelli. -/
theorem gamma_mul_studentCoordinate_rpow_eq_lintegral {α : ℝ}
    (hα : 0 < α) (z : ℂ) :
    ENNReal.ofReal (Real.Gamma α) * ENNReal.ofReal (studentCoordinate z ^ α) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (pairOverlapLaplaceAt α z r) := by
  have hx : 0 ≤ a * ‖z‖ ^ 2 := mul_nonneg witness_basic.2.1.le (sq_nonneg _)
  have hreal := pairOverlap_laplace_integral hα hx
  have hI := integrableOn_pairOverlapLaplaceAt hα z
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] pairOverlapLaplaceAt α z := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact pairOverlapLaplaceAt_nonneg hr.le
  calc
    ENNReal.ofReal (Real.Gamma α) * ENNReal.ofReal (studentCoordinate z ^ α) =
        ENNReal.ofReal ((1 + a * ‖z‖ ^ 2) ^ (-α) * Real.Gamma α) := by
      rw [studentCoordinate_rpow_eq]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      exact mul_comm _ _
    _ = ENNReal.ofReal (∫ r in Ioi (0 : ℝ), pairOverlapLaplaceAt α z r) := by
      simpa only [pairOverlapLaplaceAt] using congrArg ENNReal.ofReal hreal.symm
    _ = _ := ofReal_integral_eq_lintegral_ofReal hI hnonneg

private theorem measurable_laplace_ofReal (α : ℝ) :
    Measurable (Function.uncurry (fun z : ℂ => fun r =>
      ENNReal.ofReal (pairOverlapLaplaceAt α z r))) := by
  exact ENNReal.measurable_ofReal.comp (measurable_pairOverlapLaplaceAt α)

/-- Exact Tonelli exchange for two Student factors in one complex
coordinate. -/
theorem studentConvolution_laplace_tonelli {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (h : ℂ) :
    ENNReal.ofReal (Real.Gamma α) * ENNReal.ofReal (Real.Gamma β) *
        (∫⁻ z : ℂ, ENNReal.ofReal
          (studentCoordinate z ^ α * studentCoordinate (z + h) ^ β)) =
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), ∫⁻ z : ℂ,
        ENNReal.ofReal
          (pairOverlapLaplaceAt α z r * pairOverlapLaplaceAt β (z + h) t) := by
  let Gα : ℝ≥0∞ := ENNReal.ofReal (Real.Gamma α)
  let Gβ : ℝ≥0∞ := ENNReal.ofReal (Real.Gamma β)
  let K : ℂ → ℝ → ℝ → ℝ≥0∞ := fun z r t =>
    ENNReal.ofReal (pairOverlapLaplaceAt α z r *
      pairOverlapLaplaceAt β (z + h) t)
  have hK : Measurable (fun p : (ℂ × ℝ) × ℝ => K p.1.1 p.1.2 p.2) := by
    dsimp only [K]
    unfold pairOverlapLaplaceAt pairOverlapLaplaceKernel
    fun_prop
  calc
    Gα * Gβ * (∫⁻ z : ℂ, ENNReal.ofReal
        (studentCoordinate z ^ α * studentCoordinate (z + h) ^ β)) =
        ∫⁻ z : ℂ, (Gα * Gβ) * ENNReal.ofReal
          (studentCoordinate z ^ α * studentCoordinate (z + h) ^ β) := by
      rw [lintegral_const_mul]
      exact ENNReal.measurable_ofReal.comp
        ((measurable_studentCoordinate.pow_const α).mul
          ((measurable_studentCoordinate.comp (measurable_id.add_const h)).pow_const β))
    _ = ∫⁻ z : ℂ,
        (Gα * ENNReal.ofReal (studentCoordinate z ^ α)) *
          (Gβ * ENNReal.ofReal (studentCoordinate (z + h) ^ β)) := by
      apply lintegral_congr
      intro z
      have hmul := ENNReal.ofReal_mul
        (p := studentCoordinate z ^ α) (q := studentCoordinate (z + h) ^ β)
        (Real.rpow_nonneg (student_coordinate_bounds z).1.le _)
      rw [hmul]
      ac_rfl
    _ = ∫⁻ z : ℂ, (∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal (pairOverlapLaplaceAt α z r)) *
        (∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (pairOverlapLaplaceAt β (z + h) t)) := by
      apply lintegral_congr
      intro z
      rw [show Gα * ENNReal.ofReal (studentCoordinate z ^ α) =
          ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (pairOverlapLaplaceAt α z r) from
        gamma_mul_studentCoordinate_rpow_eq_lintegral hα z]
      rw [show Gβ * ENNReal.ofReal (studentCoordinate (z + h) ^ β) =
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (pairOverlapLaplaceAt β (z + h) t) from
        gamma_mul_studentCoordinate_rpow_eq_lintegral hβ (z + h)]
    _ = ∫⁻ z : ℂ, ∫⁻ r in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), K z r t := by
      apply lintegral_congr
      intro z
      have hma : AEMeasurable (fun r : ℝ =>
          ENNReal.ofReal (pairOverlapLaplaceAt α z r))
          (volume.restrict (Ioi 0)) := by
        apply Measurable.aemeasurable
        unfold pairOverlapLaplaceAt pairOverlapLaplaceKernel
        fun_prop
      have hmb : AEMeasurable (fun t : ℝ =>
          ENNReal.ofReal (pairOverlapLaplaceAt β (z + h) t))
          (volume.restrict (Ioi 0)) := by
        apply Measurable.aemeasurable
        unfold pairOverlapLaplaceAt pairOverlapLaplaceKernel
        fun_prop
      rw [← lintegral_lintegral_mul hma hmb]
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      dsimp only [K]
      rw [ENNReal.ofReal_mul (pairOverlapLaplaceAt_nonneg hr.le)]
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), ∫⁻ z : ℂ, K z r t := by
      have hswap1 : AEMeasurable (Function.uncurry (fun z : ℂ => fun r : ℝ =>
          ∫⁻ t in Ioi (0 : ℝ), K z r t))
          (volume.prod (volume.restrict (Ioi 0))) := by
        exact hK.aemeasurable.lintegral_prod_right'
      rw [lintegral_lintegral_swap hswap1]
      apply lintegral_congr
      intro r
      have hswap2 : AEMeasurable (Function.uncurry (fun z : ℂ => fun t : ℝ =>
          K z r t)) (volume.prod (volume.restrict (Ioi 0))) := by
        apply Measurable.aemeasurable
        dsimp only [K]
        unfold pairOverlapLaplaceAt pairOverlapLaplaceKernel
        fun_prop
      rw [lintegral_lintegral_swap hswap2]
    _ = _ := rfl

end UnitDistance.Witness
