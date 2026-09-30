module

public import UnitDistance.PairOverlapBetaReduction
public import UnitDistance.PairOverlapConvolution

@[expose] public section
set_option backward.privateInPublic true


/-! Finite real beta integrals for the actual Student convolution. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal

namespace UnitDistance.Witness

theorem integrable_studentCoordinate_mul {α β : ℝ}
    (hα : 1 < α) (hβ : 0 ≤ β) (h : ℂ) :
    Integrable (fun z : ℂ => studentCoordinate z ^ α * studentCoordinate (z + h) ^ β) := by
  apply (integrable_studentWeight witness_basic.2.1 hα).mono'
  · have hm : Measurable (fun z : ℂ =>
        studentCoordinate z ^ α * studentCoordinate (z + h) ^ β) := by
      unfold studentCoordinate
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards with z
    have hz : 0 < studentCoordinate z ∧ studentCoordinate z ≤ 1 := student_coordinate_bounds z
    have hy : 0 < studentCoordinate (z + h) ∧ studentCoordinate (z + h) ≤ 1 :=
      student_coordinate_bounds (z + h)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg hz.1.le _) (Real.rpow_nonneg hy.1.le _))]
    calc
      _ ≤ studentCoordinate z ^ α := mul_le_of_le_one_right
        (Real.rpow_nonneg hz.1.le _) (Real.rpow_le_one hy.1.le hy.2 hβ)
      _ = studentWeight a α z := by
        unfold studentCoordinate studentWeight
        rw [Real.inv_rpow (by positivity [witness_basic.2.1]),
          Real.rpow_neg (by positivity [witness_basic.2.1])]

theorem integrableOn_pairOverlapBetaKernel {α β : ℝ}
    (hα : 1 ≤ α) (hβ : 1 ≤ β) (h : ℂ) :
    IntegrableOn (pairOverlapBetaKernel α β h) (Ioo 0 1) := by
  have hI : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 1) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  apply hI.mono'
  · have hm : Measurable (pairOverlapBetaKernel α β h) := by
      unfold pairOverlapBetaKernel
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (pairOverlapBetaKernel_nonneg h hv)]
    have hX : 0 ≤ a * v * (1 - v) * ‖h‖ ^ 2 := by
      positivity [witness_basic.2.1, hv.1, sub_pos.mpr hv.2]
    have h1 := Real.rpow_le_one hv.1.le hv.2.le (sub_nonneg.mpr hα)
    have h2 := Real.rpow_le_one (sub_pos.mpr hv.2).le
      (by linarith [hv.1] : 1 - v ≤ 1) (sub_nonneg.mpr hβ)
    have h3 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith : 1 ≤ 1 +
      a * v * (1 - v) * ‖h‖ ^ 2) (by linarith : -(α + β - 1) ≤ 0)
    unfold pairOverlapBetaKernel
    calc
      _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul h1 h2
        (Real.rpow_nonneg (sub_pos.mpr hv.2).le _) (by norm_num)) h3
        (Real.rpow_nonneg (by linarith) _) (by norm_num)
      _ = 1 := by norm_num

/-- The ordinary real Student convolution with the normalized beta density. -/
theorem studentConvolution_beta_integral {α β : ℝ}
    (hα : 1 < α) (hβ : 1 < β) (h : ℂ) :
    (∫ z : ℂ, studentCoordinate z ^ α * studentCoordinate (z + h) ^ β) =
      (Real.pi / (a * (α + β - 1))) *
        (Real.Gamma (α + β) / (Real.Gamma α * Real.Gamma β)) *
          ∫ v in Ioo (0 : ℝ) 1, pairOverlapBetaKernel α β h v := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hA : 0 < α + β - 1 := by linarith
  have hGα := Real.Gamma_pos_of_pos hα0
  have hGβ := Real.Gamma_pos_of_pos hβ0
  have hGA := Real.Gamma_pos_of_pos hA
  have hI := integrable_studentCoordinate_mul hα hβ0.le h
  have hJ := integrableOn_pairOverlapBetaKernel hα.le hβ.le h
  have hnI : 0 ≤ᵐ[volume] (fun z : ℂ =>
      studentCoordinate z ^ α * studentCoordinate (z + h) ^ β) := by
    filter_upwards with z
    exact mul_nonneg (Real.rpow_nonneg (student_coordinate_bounds z).1.le _)
      (Real.rpow_nonneg (student_coordinate_bounds (z + h)).1.le _)
  have hnJ : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] pairOverlapBetaKernel α β h := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with v hv
    exact pairOverlapBetaKernel_nonneg h hv
  have he := studentConvolution_beta_lintegral hα0 hβ0 (by linarith) h
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnI,
    ← ofReal_integral_eq_lintegral_ofReal hJ hnJ] at he
  have hr := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hGα.le,
    ENNReal.toReal_ofReal hGβ.le, ENNReal.toReal_ofReal (integral_nonneg_of_ae hnI),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnJ),
    ENNReal.toReal_ofReal (mul_nonneg
      (div_nonneg Real.pi_pos.le witness_basic.2.1.le) hGA.le)] at hr
  have hrec : Real.Gamma (α + β) = (α + β - 1) * Real.Gamma (α + β - 1) := by
    convert Real.Gamma_add_one hA.ne' using 1
    congr 1
    ring
  calc
    _ = ((Real.pi / a * Real.Gamma (α + β - 1)) *
        ∫ v in Ioo (0 : ℝ) 1, pairOverlapBetaKernel α β h v) /
          (Real.Gamma α * Real.Gamma β) := by
      apply (eq_div_iff (mul_ne_zero hGα.ne' hGβ.ne')).mpr
      simpa only [mul_comm] using hr
    _ = _ := by
      rw [hrec]
      field_simp

theorem pairOverlapCoordinateConvolution_beta (i k : Fin 4) (h : ℂ) :
    pairOverlapCoordinateConvolution i k h =
      (Real.pi / (a * (s + (i : ℕ) + (s + (k : ℕ)) - 1))) *
        (Real.Gamma (s + (i : ℕ) + (s + (k : ℕ))) /
          (Real.Gamma (s + (i : ℕ)) * Real.Gamma (s + (k : ℕ)))) *
          ∫ v in Ioo (0 : ℝ) 1,
            pairOverlapBetaKernel (s + (i : ℕ)) (s + (k : ℕ)) h v := by
  apply studentConvolution_beta_integral
  · have hs : 1 < s := by norm_num [s]
    linarith [Nat.cast_nonneg (α := ℝ) (i : ℕ)]
  · have hs : 1 < s := by norm_num [s]
    linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]

end UnitDistance.Witness
