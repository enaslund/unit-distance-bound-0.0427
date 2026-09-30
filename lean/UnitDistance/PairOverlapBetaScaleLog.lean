module

public import UnitDistance.PairOverlapBetaLogMoments

@[expose] public section
set_option backward.privateInPublic true


/-! The beta expectation of the logarithmic hyperbola scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace UnitDistance.Witness

theorem log_inverse_beta_scale {t v : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    Real.log (1 / (a * Real.sqrt (t*(1-t)*v*(1-v)))) =
      Real.log (1/a) - Real.log (t*(1-t))/2 - Real.log (v*(1-v))/2 := by
  have ha := witness_basic.2.1
  have ht' : 0 < t*(1-t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  have hv' : 0 < v*(1-v) := mul_pos hv.1 (sub_pos.mpr hv.2)
  rw [show t*(1-t)*v*(1-v) = (t*(1-t))*(v*(1-v)) by ring]
  rw [one_div, Real.log_inv, Real.log_mul ha.ne'
    (Real.sqrt_pos.mpr (mul_pos ht' hv')).ne', Real.log_sqrt (mul_pos ht' hv').le,
    Real.log_mul ht'.ne' hv'.ne', one_div, Real.log_inv]
  ring

theorem integral_pairOverlapBetaDensity_affine_log (i k : Fin 4) (C D : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1,
      pairOverlapBetaDensity i k t * (C + D * Real.log (t*(1-t)))) =
      C + D * ((Complex.digamma ((s + (i : ℕ) : ℝ) : ℂ)).re +
        (Complex.digamma ((s + (k : ℕ) : ℝ) : ℂ)).re -
          2 * (Complex.digamma ((s + (i : ℕ) + (s + (k : ℕ)) : ℝ) : ℂ)).re) := by
  have heq : (fun t => pairOverlapBetaDensity i k t * (C + D * Real.log (t*(1-t)))) =
      (fun t => C * pairOverlapBetaDensity i k t +
        D * (pairOverlapBetaDensity i k t * Real.log (t*(1-t)))) := by
    funext t
    ring
  rw [heq, integral_add ((integrableOn_pairOverlapBetaDensity i k).const_mul C)
    ((integrableOn_pairOverlapBetaDensity_mul_log_product i k).const_mul D),
    integral_const_mul, integral_const_mul, integral_pairOverlapBetaDensity,
    integral_pairOverlapBetaDensity_mul_log_product, mul_one]

theorem integral_pairOverlapBetaDensity_log_scale (i j k l : Fin 4) :
    (∫ t in Ioo (0 : ℝ) 1, ∫ v in Ioo (0 : ℝ) 1,
      pairOverlapBetaDensity i k t * pairOverlapBetaDensity j l v *
        Real.log (1 / (a * Real.sqrt (t*(1-t)*v*(1-v))))) =
      Real.log (1/a) -
        ((Complex.digamma ((s + (i : ℕ) : ℝ) : ℂ)).re +
          (Complex.digamma ((s + (k : ℕ) : ℝ) : ℂ)).re -
            2 * (Complex.digamma ((s + (i : ℕ) + (s + (k : ℕ)) : ℝ) : ℂ)).re) / 2 -
        ((Complex.digamma ((s + (j : ℕ) : ℝ) : ℂ)).re +
          (Complex.digamma ((s + (l : ℕ) : ℝ) : ℂ)).re -
            2 * (Complex.digamma ((s + (j : ℕ) + (s + (l : ℕ)) : ℝ) : ℂ)).re) / 2 := by
  have hinner (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      (∫ v in Ioo (0 : ℝ) 1, pairOverlapBetaDensity i k t * pairOverlapBetaDensity j l v *
        Real.log (1 / (a * Real.sqrt (t*(1-t)*v*(1-v))))) =
      pairOverlapBetaDensity i k t * (Real.log (1/a) - Real.log (t*(1-t))/2 -
        ((Complex.digamma ((s + (j : ℕ) : ℝ) : ℂ)).re +
          (Complex.digamma ((s + (l : ℕ) : ℝ) : ℂ)).re -
            2 * (Complex.digamma ((s + (j : ℕ) + (s + (l : ℕ)) : ℝ) : ℂ)).re) / 2) := by
    calc
      _ = ∫ v in Ioo (0 : ℝ) 1, pairOverlapBetaDensity i k t *
          (pairOverlapBetaDensity j l v *
            ((Real.log (1/a) - Real.log (t*(1-t))/2) + (-1/2)*Real.log (v*(1-v)))) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro v hv
        dsimp only
        rw [log_inverse_beta_scale ht hv]
        ring
      _ = _ := by
        rw [integral_const_mul, integral_pairOverlapBetaDensity_affine_log]
        ring
  calc
    _ = ∫ t in Ioo (0 : ℝ) 1, pairOverlapBetaDensity i k t *
        ((Real.log (1/a) -
          ((Complex.digamma ((s + (j : ℕ) : ℝ) : ℂ)).re +
            (Complex.digamma ((s + (l : ℕ) : ℝ) : ℂ)).re -
              2 * (Complex.digamma ((s + (j : ℕ) + (s + (l : ℕ)) : ℝ) : ℂ)).re)/2) +
                (-1/2)*Real.log (t*(1-t))) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp only
      rw [hinner t ht]
      ring
    _ = _ := by
      rw [integral_pairOverlapBetaDensity_affine_log]
      ring

end UnitDistance.Witness
