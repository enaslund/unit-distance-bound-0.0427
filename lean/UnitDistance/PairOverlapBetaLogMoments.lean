module

public import UnitDistance.PairOverlapBetaDensity
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! Exact logarithmic moments of the beta densities in the overlap. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology

namespace UnitDistance

def realBetaWeight (α β t : ℝ) : ℝ := t ^ (α - 1) * (1 - t) ^ (β - 1)

theorem realBetaWeight_nonneg {α β t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ realBetaWeight α β t := by
  unfold realBetaWeight
  positivity [ht.1, sub_pos.mpr ht.2]

theorem realBetaWeight_le_one {α β t : ℝ} (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (ht : t ∈ Ioo (0 : ℝ) 1) : realBetaWeight α β t ≤ 1 := by
  unfold realBetaWeight
  exact mul_le_one₀ (Real.rpow_le_one ht.1.le ht.2.le (sub_nonneg.mpr hα))
    (Real.rpow_nonneg (sub_pos.mpr ht.2).le _)
    (Real.rpow_le_one (sub_pos.mpr ht.2).le (by linarith [ht.1]) (sub_nonneg.mpr hβ))

theorem integrableOn_realBetaWeight {α β : ℝ} (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    IntegrableOn (realBetaWeight α β) (Ioo (0 : ℝ) 1) := by
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 1) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  apply hc.mono'
  · have hm : Measurable (realBetaWeight α β) := by unfold realBetaWeight; fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (realBetaWeight_nonneg ht)]
    exact realBetaWeight_le_one hα hβ ht

theorem integral_realBetaWeight {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ t in Ioo (0 : ℝ) 1, realBetaWeight α β t) =
      Real.Gamma α * Real.Gamma β / Real.Gamma (α + β) := by
  apply Complex.ofReal_injective
  calc
    _ = ∫ t in Ioo (0 : ℝ) 1, (realBetaWeight α β t : ℂ) := integral_complex_ofReal.symm
    _ = ∫ t in Ioo (0 : ℝ) 1,
        (t : ℂ) ^ ((α : ℂ) - 1) * (1 - (t : ℂ)) ^ ((β : ℂ) - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp only [realBetaWeight]
      rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le,
        Complex.ofReal_cpow (sub_pos.mpr ht.2).le]
      push_cast
      rfl
    _ = Complex.betaIntegral (α : ℂ) (β : ℂ) := by
      rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
        integral_Ioc_eq_integral_Ioo]
    _ = _ := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hα) (by simpa using hβ)]
      rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
        Complex.Gamma_ofReal]
      norm_cast

theorem hasDerivAt_realGamma_digamma {α : ℝ} (hα : 0 < α) :
    HasDerivAt Real.Gamma
      (Real.Gamma α * (Complex.digamma (α : ℂ)).re) α := by
  have hc : DifferentiableAt ℂ Complex.Gamma (α : ℂ) :=
    Complex.differentiableAt_Gamma _ (by
      intro n hn
      have hr := congrArg Complex.re hn
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
      linarith [Nat.cast_nonneg (α := ℝ) n])
  have hd := hc.hasDerivAt.real_of_complex
  have hr : Real.Gamma α * (Complex.digamma (α : ℂ)).re =
      (deriv Complex.Gamma (α : ℂ)).re := by
    rw [Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal, Complex.div_ofReal_re]
    field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα)]
  rw [hr]
  exact hd

theorem hasDerivAt_integral_realBetaWeight {α β : ℝ} (hα : 1 < α) (hβ : 1 ≤ β) :
    IntegrableOn (fun t => realBetaWeight α β t * Real.log t) (Ioo (0 : ℝ) 1) ∧
      HasDerivAt (fun x => ∫ t in Ioo (0 : ℝ) 1, realBetaWeight x β t)
        (∫ t in Ioo (0 : ℝ) 1, realBetaWeight α β t * Real.log t) α := by
  have hlog : IntegrableOn Real.log (Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      intervalIntegral.intervalIntegrable_log'
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t : ℝ => realBetaWeight x β t)
    (F' := fun x t : ℝ => realBetaWeight x β t * Real.log t)
    (bound := fun t : ℝ => |Real.log t|) (s := Ioi (1 : ℝ))
    (isOpen_Ioi.mem_nhds hα)
  · apply Filter.Eventually.of_forall
    intro x
    have hm : Measurable (realBetaWeight x β) := by unfold realBetaWeight; fun_prop
    exact hm.aestronglyMeasurable
  · exact integrableOn_realBetaWeight hα.le hβ
  · have hm : Measurable (fun t => realBetaWeight α β t * Real.log t) := by
      unfold realBetaWeight
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    intro x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (realBetaWeight_nonneg ht)]
    exact mul_le_of_le_one_left (abs_nonneg _) (realBetaWeight_le_one hx.le hβ ht)
  · exact hlog.abs
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    intro x hx
    have hd := ((hasDerivAt_id x).sub_const (1 : ℝ)).const_rpow ht.1
    have hdm := hd.mul_const ((1-t)^(β-1))
    simp only [id_eq] at hdm
    convert! hdm using 1 <;> unfold realBetaWeight <;> ring

theorem integral_realBetaWeight_mul_log {α β : ℝ} (hα : 1 < α) (hβ : 1 ≤ β) :
    (∫ t in Ioo (0 : ℝ) 1, realBetaWeight α β t * Real.log t) =
      (Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)) *
        ((Complex.digamma (α : ℂ)).re - (Complex.digamma ((α + β : ℝ) : ℂ)).re) := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hs : 0 < α + β := by linarith
  have hga := hasDerivAt_realGamma_digamma hα0
  have hgs := (hasDerivAt_realGamma_digamma hs).comp α ((hasDerivAt_id α).add_const β)
  simp only [Function.comp_def, id_eq, mul_one] at hgs
  have hgs0 : Real.Gamma (α + β) ≠ 0 := (Real.Gamma_pos_of_pos hs).ne'
  have hdQ : HasDerivAt (fun x => Real.Gamma x * Real.Gamma β / Real.Gamma (x + β))
      ((Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)) *
        ((Complex.digamma (α : ℂ)).re - (Complex.digamma ((α + β : ℝ) : ℂ)).re)) α := by
    convert! (hga.mul_const (Real.Gamma β)).div hgs hgs0 using 1
    field_simp
    <;> ring
  have heq : (fun x => ∫ t in Ioo (0 : ℝ) 1, realBetaWeight x β t) =ᶠ[𝓝 α]
      (fun x => Real.Gamma x * Real.Gamma β / Real.Gamma (x + β)) := by
    filter_upwards [eventually_gt_nhds hα0] with x hx
    exact integral_realBetaWeight hx hβ0
  exact (hasDerivAt_integral_realBetaWeight hα hβ).2.unique
    (hdQ.congr_of_eventuallyEq heq)

theorem integral_Ioo_one_sub (f : ℝ → ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, f (1-t)) = ∫ t in Ioo (0 : ℝ) 1, f t := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) f 1
  simpa only [sub_self, sub_zero, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo] using h

theorem integrableOn_Ioo_one_sub (f : ℝ → ℝ) (hf : IntegrableOn f (Ioo (0 : ℝ) 1)) :
    IntegrableOn (fun t => f (1-t)) (Ioo (0 : ℝ) 1) := by
  have hI : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hf
  have hr := hI.comp_sub_left 1
  have hI' : IntervalIntegrable (fun t => f (1-t)) volume 0 1 := by simpa using hr.symm
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hI'

theorem realBetaWeight_one_sub (α β t : ℝ) :
    realBetaWeight β α (1-t) = realBetaWeight α β t := by
  unfold realBetaWeight
  rw [sub_sub_cancel]
  exact mul_comm _ _

theorem integrableOn_realBetaWeight_mul_log_one_sub {α β : ℝ}
    (hα : 1 ≤ α) (hβ : 1 < β) :
    IntegrableOn (fun t => realBetaWeight α β t * Real.log (1-t)) (Ioo (0 : ℝ) 1) := by
  have hi := integrableOn_Ioo_one_sub (fun t => realBetaWeight β α t * Real.log t)
    (hasDerivAt_integral_realBetaWeight hβ hα).1
  simpa only [realBetaWeight_one_sub] using hi

theorem integral_realBetaWeight_mul_log_one_sub {α β : ℝ}
    (hα : 1 ≤ α) (hβ : 1 < β) :
    (∫ t in Ioo (0 : ℝ) 1, realBetaWeight α β t * Real.log (1-t)) =
      (Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)) *
        ((Complex.digamma (β : ℂ)).re - (Complex.digamma ((α + β : ℝ) : ℂ)).re) := by
  have hi := integral_Ioo_one_sub (fun t => realBetaWeight β α t * Real.log t)
  simp only [realBetaWeight_one_sub] at hi
  rw [hi, integral_realBetaWeight_mul_log hβ hα, add_comm β α, mul_comm (Real.Gamma β)]

namespace Witness

theorem integral_pairOverlapBetaDensity (i k : Fin 4) :
    (∫ t in Ioo (0 : ℝ) 1, pairOverlapBetaDensity i k t) = 1 := by
  have hα : 0 < s + (i : ℕ) := by positivity [witness_basic.1]
  have hβ : 0 < s + (k : ℕ) := by positivity [witness_basic.1]
  have heq : pairOverlapBetaDensity i k =
      fun t => pairOverlapBetaNormalization i k * realBetaWeight (s + (i : ℕ)) (s + (k : ℕ)) t := by
    funext t
    unfold pairOverlapBetaDensity realBetaWeight
    ring
  rw [heq, integral_const_mul, integral_realBetaWeight hα hβ]
  unfold pairOverlapBetaNormalization
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα), ne_of_gt (Real.Gamma_pos_of_pos hβ),
    ne_of_gt (Real.Gamma_pos_of_pos (add_pos hα hβ))]

theorem integral_pairOverlapBetaDensity_mul_log (i k : Fin 4) :
    (∫ t in Ioo (0 : ℝ) 1, pairOverlapBetaDensity i k t * Real.log t) =
      (Complex.digamma ((s + (i : ℕ) : ℝ) : ℂ)).re -
        (Complex.digamma ((s + (i : ℕ) + (s + (k : ℕ)) : ℝ) : ℂ)).re := by
  have hs : 1 < s := by norm_num [s]
  have hα : 1 < s + (i : ℕ) := by linarith [Nat.cast_nonneg (α := ℝ) (i : ℕ)]
  have hβ : 1 < s + (k : ℕ) := by linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
  have heq : (fun t => pairOverlapBetaDensity i k t * Real.log t) =
      fun t => pairOverlapBetaNormalization i k *
        (realBetaWeight (s + (i : ℕ)) (s + (k : ℕ)) t * Real.log t) := by
    funext t
    unfold pairOverlapBetaDensity realBetaWeight
    ring
  rw [heq, integral_const_mul, integral_realBetaWeight_mul_log hα hβ.le]
  unfold pairOverlapBetaNormalization
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos (by linarith : 0 < s + (i : ℕ))),
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith : 0 < s + (k : ℕ))),
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith : 0 < s + (i : ℕ) + (s + (k : ℕ))))]

theorem pairOverlapBetaDensity_one_sub (i k : Fin 4) (t : ℝ) :
    pairOverlapBetaDensity k i (1-t) = pairOverlapBetaDensity i k t := by
  unfold pairOverlapBetaDensity pairOverlapBetaNormalization
  rw [sub_sub_cancel]
  rw [add_comm (s + (k : ℕ)) (s + (i : ℕ)),
    mul_comm (Real.Gamma (s + (k : ℕ))) (Real.Gamma (s + (i : ℕ)))]
  ring

theorem integral_pairOverlapBetaDensity_mul_log_one_sub (i k : Fin 4) :
    (∫ t in Ioo (0 : ℝ) 1, pairOverlapBetaDensity i k t * Real.log (1-t)) =
      (Complex.digamma ((s + (k : ℕ) : ℝ) : ℂ)).re -
        (Complex.digamma ((s + (i : ℕ) + (s + (k : ℕ)) : ℝ) : ℂ)).re := by
  have hi := integral_Ioo_one_sub (fun t => pairOverlapBetaDensity k i t * Real.log t)
  simp only [pairOverlapBetaDensity_one_sub] at hi
  rw [hi, integral_pairOverlapBetaDensity_mul_log, add_comm (s + (k : ℕ)) (s + (i : ℕ))]

theorem integrableOn_pairOverlapBetaDensity (i k : Fin 4) :
    IntegrableOn (pairOverlapBetaDensity i k) (Ioo (0 : ℝ) 1) := by
  have hs : 1 < s := by norm_num [s]
  have hα : 1 ≤ s + (i : ℕ) := by linarith [Nat.cast_nonneg (α := ℝ) (i : ℕ)]
  have hβ : 1 ≤ s + (k : ℕ) := by linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
  apply ((integrableOn_realBetaWeight hα hβ).const_mul (pairOverlapBetaNormalization i k)).congr
  filter_upwards with t
  unfold realBetaWeight pairOverlapBetaDensity
  ring

theorem integrableOn_pairOverlapBetaDensity_mul_log (i k : Fin 4) :
    IntegrableOn (fun t => pairOverlapBetaDensity i k t * Real.log t) (Ioo (0 : ℝ) 1) := by
  have hs : 1 < s := by norm_num [s]
  have hα : 1 < s + (i : ℕ) := by linarith [Nat.cast_nonneg (α := ℝ) (i : ℕ)]
  have hβ : 1 ≤ s + (k : ℕ) := by linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
  apply (((hasDerivAt_integral_realBetaWeight hα hβ).1).const_mul
    (pairOverlapBetaNormalization i k)).congr
  filter_upwards with t
  unfold realBetaWeight pairOverlapBetaDensity
  ring

theorem integrableOn_pairOverlapBetaDensity_mul_log_one_sub (i k : Fin 4) :
    IntegrableOn (fun t => pairOverlapBetaDensity i k t * Real.log (1-t)) (Ioo (0 : ℝ) 1) := by
  have hi := integrableOn_Ioo_one_sub (fun t => pairOverlapBetaDensity k i t * Real.log t)
    (integrableOn_pairOverlapBetaDensity_mul_log k i)
  simpa only [pairOverlapBetaDensity_one_sub] using hi

theorem integral_pairOverlapBetaDensity_mul_log_product (i k : Fin 4) :
    (∫ t in Ioo (0 : ℝ) 1, pairOverlapBetaDensity i k t * Real.log (t*(1-t))) =
      (Complex.digamma ((s + (i : ℕ) : ℝ) : ℂ)).re +
        (Complex.digamma ((s + (k : ℕ) : ℝ) : ℂ)).re -
          2 * (Complex.digamma ((s + (i : ℕ) + (s + (k : ℕ)) : ℝ) : ℂ)).re := by
  have heq : (fun t => pairOverlapBetaDensity i k t * Real.log (t*(1-t))) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)]
        (fun t => pairOverlapBetaDensity i k t * Real.log t +
          pairOverlapBetaDensity i k t * Real.log (1-t)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [Real.log_mul ht.1.ne' (sub_pos.mpr ht.2).ne']
    ring
  rw [integral_congr_ae heq, integral_add (integrableOn_pairOverlapBetaDensity_mul_log i k)
    (integrableOn_pairOverlapBetaDensity_mul_log_one_sub i k),
    integral_pairOverlapBetaDensity_mul_log, integral_pairOverlapBetaDensity_mul_log_one_sub]
  ring

theorem integrableOn_pairOverlapBetaDensity_mul_log_product (i k : Fin 4) :
    IntegrableOn (fun t => pairOverlapBetaDensity i k t * Real.log (t*(1-t))) (Ioo (0 : ℝ) 1) := by
  apply ((integrableOn_pairOverlapBetaDensity_mul_log i k).add
    (integrableOn_pairOverlapBetaDensity_mul_log_one_sub i k)).congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  rw [Real.log_mul ht.1.ne' (sub_pos.mpr ht.2).ne']
  simp only [Pi.add_apply]
  ring

end Witness
end UnitDistance
