module

public import UnitDistance.PairOverlapBetaChange
public import UnitDistance.PairOverlapGaussianReduction

@[expose] public section
set_option backward.privateInPublic true


/-! Exact Feynman-parameter reduction of the Student convolution. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal

namespace UnitDistance

theorem integrableOn_pairOverlapLaplaceKernel {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) :
    IntegrableOn (pairOverlapLaplaceKernel α x) (Ioi 0) := by
  apply (Real.GammaIntegral_convergent hα).mono'
  · have hm : Measurable (pairOverlapLaplaceKernel α x) := by
      unfold pairOverlapLaplaceKernel
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (pairOverlapLaplaceKernel_nonneg hr.le)]
    unfold pairOverlapLaplaceKernel
    have he : Real.exp (-(r * (1 + x))) ≤ Real.exp (-r) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hr.le hx]
    calc
      _ ≤ r ^ (α - 1) * Real.exp (-r) :=
        mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hr.le _)
      _ = _ := mul_comm _ _

theorem lintegral_pairOverlapLaplaceKernel {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (pairOverlapLaplaceKernel α x r)) =
      ENNReal.ofReal ((1 + x) ^ (-α) * Real.Gamma α) := by
  rw [← pairOverlap_laplace_integral hα hx]
  symm
  apply ofReal_integral_eq_lintegral_ofReal (integrableOn_pairOverlapLaplaceKernel hα hx)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  exact pairOverlapLaplaceKernel_nonneg hr.le

namespace Witness

theorem pairOverlapReducedLaplaceKernel_beta {α β u v : ℝ} (h : ℂ)
    (hu : 0 < u) (hv : v ∈ Ioo (0 : ℝ) 1) :
    u * pairOverlapReducedLaplaceKernel α β h (u * (1 - v)) (u * v) =
      (Real.pi / a * (1 - v) ^ (α - 1) * v ^ (β - 1)) *
        pairOverlapLaplaceKernel (α + β - 1) (a * v * (1 - v) * ‖h‖ ^ 2) u := by
  have hv' : 0 < 1 - v := sub_pos.mpr hv.2
  have hu0 : u ≠ 0 := hu.ne'
  have ha0 : a ≠ 0 := witness_basic.2.1.ne'
  have hsum : u * (1 - v) + u * v = u := by ring
  have hquot : u * (1 - v) * (u * v) / u = u * v * (1 - v) := by
    field_simp
    <;> ring
  have hp : u ^ (α - 1) * u ^ (β - 1) = u ^ (α + β - 1 - 1) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  unfold pairOverlapReducedLaplaceKernel pairOverlapLaplaceKernel
  rw [hsum, hquot, Real.mul_rpow hu.le hv'.le, Real.mul_rpow hu.le hv.1.le]
  have he : Real.exp (-u) * Real.exp (-(a * (u * v * (1 - v))) * ‖h‖ ^ 2) =
      Real.exp (-(u * (1 + a * v * (1 - v) * ‖h‖ ^ 2))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.pi / a * (1 - v) ^ (α - 1) * v ^ (β - 1)) *
        (u ^ (α - 1) * u ^ (β - 1)) *
        (Real.exp (-u) * Real.exp (-(a * (u * v * (1 - v))) * ‖h‖ ^ 2)) := by
      field_simp
      <;> ring
    _ = _ := by rw [hp, he]; ring

theorem pairOverlapReducedLaplaceKernel_beta_first {α β u v : ℝ} (h : ℂ)
    (hu : 0 < u) (hv : v ∈ Ioo (0 : ℝ) 1) :
    u * pairOverlapReducedLaplaceKernel α β h (u * v) (u * (1 - v)) =
      (Real.pi / a * v ^ (α - 1) * (1 - v) ^ (β - 1)) *
        pairOverlapLaplaceKernel (α + β - 1) (a * v * (1 - v) * ‖h‖ ^ 2) u := by
  have hs : pairOverlapReducedLaplaceKernel α β h (u * v) (u * (1 - v)) =
      pairOverlapReducedLaplaceKernel β α h (u * (1 - v)) (u * v) := by
    unfold pairOverlapReducedLaplaceKernel
    rw [add_comm (u * v), mul_comm (u * v) (u * (1 - v))]
    ring
  rw [hs, pairOverlapReducedLaplaceKernel_beta h hu hv, add_comm β α]
  ring

def pairOverlapBetaKernel (α β : ℝ) (h : ℂ) (v : ℝ) : ℝ :=
  v ^ (α - 1) * (1 - v) ^ (β - 1) *
    (1 + a * v * (1 - v) * ‖h‖ ^ 2) ^ (-(α + β - 1))

theorem pairOverlapBetaKernel_nonneg {α β v : ℝ} (h : ℂ)
    (hv : v ∈ Ioo (0 : ℝ) 1) : 0 ≤ pairOverlapBetaKernel α β h v := by
  unfold pairOverlapBetaKernel
  positivity [witness_basic.2.1, hv.1, sub_pos.mpr hv.2]

set_option maxHeartbeats 2000000 in
/-- The exact one-dimensional beta representation, before imposing finiteness. -/
theorem studentConvolution_beta_lintegral {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hA : 1 < α + β) (h : ℂ) :
    ENNReal.ofReal (Real.Gamma α) * ENNReal.ofReal (Real.Gamma β) *
        (∫⁻ z : ℂ, ENNReal.ofReal
          (studentCoordinate z ^ α * studentCoordinate (z + h) ^ β)) =
      ENNReal.ofReal (Real.pi / a * Real.Gamma (α + β - 1)) *
        ∫⁻ v in Ioo (0 : ℝ) 1, ENNReal.ofReal (pairOverlapBetaKernel α β h v) := by
  let C : ℝ → ℝ := fun v => Real.pi / a * v ^ (α - 1) * (1 - v) ^ (β - 1)
  let X : ℝ → ℝ := fun v => a * v * (1 - v) * ‖h‖ ^ 2
  let L : ℝ → ℝ → ℝ≥0∞ := fun u v =>
    ENNReal.ofReal (C v * pairOverlapLaplaceKernel (α + β - 1) (X v) u)
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (pairOverlapReducedLaplaceKernel α β h p.1 p.2)) := by
    unfold pairOverlapReducedLaplaceKernel
    fun_prop
  have hmL : Measurable (Function.uncurry L) := by
    dsimp only [L, C, X]
    unfold pairOverlapLaplaceKernel
    fun_prop
  rw [studentConvolution_laplace_reduction hα hβ h,
    lintegral_positiveQuadrant_eq_betaParameters_first _ hm]
  calc
    _ = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioo (0 : ℝ) 1, L u v := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      rw [← lintegral_const_mul]
      · apply lintegral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with v hv
        change ENNReal.ofReal u * ENNReal.ofReal
          (pairOverlapReducedLaplaceKernel α β h (u * v) (u * (1 - v))) =
          ENNReal.ofReal (C v * pairOverlapLaplaceKernel (α + β - 1) (X v) u)
        rw [← ENNReal.ofReal_mul hu.le, pairOverlapReducedLaplaceKernel_beta_first h hu hv]
      · exact hm.comp ((measurable_const.mul measurable_id).prodMk
          (measurable_const.mul (measurable_const.sub measurable_id)))
    _ = ∫⁻ v in Ioo (0 : ℝ) 1, ∫⁻ u in Ioi (0 : ℝ), L u v :=
      lintegral_lintegral_swap hmL.aemeasurable
    _ = ∫⁻ v in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.pi / a * Real.Gamma (α + β - 1)) *
          ENNReal.ofReal (pairOverlapBetaKernel α β h v) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with v hv
      have hC : 0 ≤ C v := by
        dsimp only [C]
        positivity [witness_basic.2.1, hv.1, sub_pos.mpr hv.2]
      have hX : 0 ≤ X v := by
        dsimp only [X]
        positivity [witness_basic.2.1, hv.1, sub_pos.mpr hv.2]
      dsimp only [L]
      simp_rw [ENNReal.ofReal_mul hC]
      rw [lintegral_const_mul]
      · rw [lintegral_pairOverlapLaplaceKernel (by linarith) hX]
        rw [← ENNReal.ofReal_mul hC,
          ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg Real.pi_pos.le witness_basic.2.1.le)
            (Real.Gamma_pos_of_pos (by linarith)).le)]
        congr 1
        unfold C X pairOverlapBetaKernel
        ring
      · unfold pairOverlapLaplaceKernel
        fun_prop
    _ = _ := by
      rw [lintegral_const_mul]
      unfold pairOverlapBetaKernel
      fun_prop

end Witness
end UnitDistance
