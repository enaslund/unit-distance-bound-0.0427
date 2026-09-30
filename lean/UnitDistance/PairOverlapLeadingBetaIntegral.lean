module

public import UnitDistance.PairOverlapBetaScaleLog
public import UnitDistance.PairOverlapLeadingCollection
public import UnitDistance.PairOverlapHyperbolaLeading

@[expose] public section
set_option backward.privateInPublic true


/-! The actual double beta expectation of the leading hyperbola term. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace UnitDistance.Witness

theorem integral_pairOverlapBetaDensity_affine_logs (i j k l : Fin 4) (C D E : ℝ) :
    (∫ t in Ioo (0:ℝ) 1, ∫ v in Ioo (0:ℝ) 1,
      pairOverlapBetaDensity i k t * pairOverlapBetaDensity j l v *
        (C + D*Real.log (t*(1-t)) + E*Real.log (v*(1-v)))) =
      C + D*pairOverlapBetaLogMoment i k + E*pairOverlapBetaLogMoment j l := by
  have hi (t : ℝ) :
      (∫ v in Ioo (0:ℝ) 1, pairOverlapBetaDensity i k t * pairOverlapBetaDensity j l v *
        (C + D*Real.log (t*(1-t)) + E*Real.log (v*(1-v)))) =
      pairOverlapBetaDensity i k t *
        (C + D*Real.log (t*(1-t)) + E*pairOverlapBetaLogMoment j l) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_pairOverlapBetaDensity_affine_log]
    rfl
  simp_rw [hi]
  calc
    _ = ∫ t in Ioo (0:ℝ) 1, pairOverlapBetaDensity i k t *
      ((C + E*pairOverlapBetaLogMoment j l) + D*Real.log (t*(1-t))) := by
        congr 1
        funext t
        ring
    _ = _ := by
      rw [integral_pairOverlapBetaDensity_affine_log]
      unfold pairOverlapBetaLogMoment
      ring

theorem pairOverlap_betaScale_pos_le_one {t v : ℝ}
    (ht : t ∈ Ioo (0:ℝ) 1) (hv : v ∈ Ioo (0:ℝ) 1) :
    0 < a*Real.sqrt (t*(1-t)*v*(1-v)) ∧
      a*Real.sqrt (t*(1-t)*v*(1-v)) ≤ 1 := by
  have ht0 : 0 < t*(1-t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  have hv0 : 0 < v*(1-v) := mul_pos hv.1 (sub_pos.mpr hv.2)
  have ht1 : t*(1-t) ≤ 1 := by nlinarith [sq_nonneg t]
  have hv1 : v*(1-v) ≤ 1 := by nlinarith [sq_nonneg v]
  have hp0 : 0 < t*(1-t)*v*(1-v) := by nlinarith [mul_pos ht0 hv0]
  have hp1 : t*(1-t)*v*(1-v) ≤ 1 := by nlinarith [mul_le_mul ht1 hv1 hv0.le zero_le_one]
  have hsq : Real.sqrt (t*(1-t)*v*(1-v)) ≤ 1 := (Real.sqrt_le_one).mpr hp1
  constructor
  · exact mul_pos witness_basic.2.1 (Real.sqrt_pos.mpr hp0)
  · exact le_trans (mul_le_mul_of_nonneg_left hsq witness_basic.2.1.le)
      (by norm_num [a])

theorem integral_pairOverlapBetaDensity_leading (i j k l : Fin 4) :
    (∫ t in Ioo (0:ℝ) 1, ∫ v in Ioo (0:ℝ) 1,
      pairOverlapBetaDensity i k t * pairOverlapBetaDensity j l v *
        pairHyperbolaLeading (pairOverlapBetaExponent i k) (pairOverlapBetaExponent j l)
          (a*Real.sqrt (t*(1-t)*v*(1-v)))) = pairOverlapLeadingMean i j k l := by
  have hA : 0 < pairOverlapBetaExponent i k := by
    unfold pairOverlapBetaExponent
    have hi := Nat.cast_nonneg (α := ℝ) (i:ℕ)
    have hk := Nat.cast_nonneg (α := ℝ) (k:ℕ)
    norm_num [s] at *
    linarith
  have hB : 0 < pairOverlapBetaExponent j l := by
    unfold pairOverlapBetaExponent
    have hj := Nat.cast_nonneg (α := ℝ) (j:ℕ)
    have hl := Nat.cast_nonneg (α := ℝ) (l:ℕ)
    norm_num [s] at *
    linarith
  calc
    _ = ∫ t in Ioo (0:ℝ) 1, ∫ v in Ioo (0:ℝ) 1,
        pairOverlapBetaDensity i k t * pairOverlapBetaDensity j l v *
          ((Real.log (1/a) - Real.eulerMascheroniConstant -
            ((Complex.digamma (pairOverlapBetaExponent i k : ℂ)).re +
              (Complex.digamma (pairOverlapBetaExponent j l : ℂ)).re)/2) +
            (-1/2)*Real.log (t*(1-t)) + (-1/2)*Real.log (v*(1-v))) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      apply setIntegral_congr_fun measurableSet_Ioo
      intro v hv
      dsimp only
      have hb := pairOverlap_betaScale_pos_le_one ht hv
      rw [pairHyperbolaLeading_eq_log_digamma hA hB hb.1 hb.2,
        log_inverse_beta_scale ht hv, Complex.digamma_one]
      simp only [Complex.neg_re, Complex.ofReal_re]
      ring
    _ = _ := by
      rw [integral_pairOverlapBetaDensity_affine_logs]
      unfold pairOverlapLeadingMean
      ring

end UnitDistance.Witness
