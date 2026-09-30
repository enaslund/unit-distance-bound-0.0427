module

public import UnitDistance.PairOverlapBetaFubini
public import UnitDistance.PairOverlapHyperbolaIntegrable

@[expose] public section
set_option backward.privateInPublic true


/-! Exact beta expectation of the hyperbola kernel for the actual overlap. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace UnitDistance.Witness

theorem norm_complex_exp_sq (u : ℝ) : ‖(Real.exp u : ℂ)‖^2 = Real.exp (2*u) := by
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos u)]
  exact (Real.exp_nat_mul u 2).symm

theorem pairOverlapBetaTripleKernel_reciprocal (i j k l : Fin 4) (u : ℝ) (tv : ℝ × ℝ) :
    pairOverlapBetaTripleKernel i j k l u tv =
      (pairOverlapBetaDensity i k tv.1 * pairOverlapBetaDensity j l tv.2) *
        ((1 + (a*tv.1*(1-tv.1))*Real.exp (2*u)) ^ (-pairOverlapBetaExponent i k) *
          (1 + (a*tv.2*(1-tv.2))*Real.exp (-2*u)) ^ (-pairOverlapBetaExponent j l)) := by
  unfold pairOverlapBetaTripleKernel pairOverlapBetaShiftKernel
  rw [norm_complex_exp_sq, norm_complex_exp_sq,
    show 2*(-u) = -2*u by ring]
  ring

theorem pairHyperbolaMean_beta {t v : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    pairHyperbolaMean (a*t*(1-t)) (a*v*(1-v)) =
      a * Real.sqrt (t*(1-t)*v*(1-v)) := by
  have ha := witness_basic.2.1
  have hX : 0 < a*t*(1-t) := by positivity [ht.1, sub_pos.mpr ht.2]
  have hY : 0 < a*v*(1-v) := by positivity [hv.1, sub_pos.mpr hv.2]
  have hR : 0 ≤ t*(1-t)*v*(1-v) := by
    positivity [ht.1, sub_pos.mpr ht.2, hv.1, sub_pos.mpr hv.2]
  apply (sq_eq_sq₀ (pairHyperbolaMean_pos _ _).le
    (mul_nonneg ha.le (Real.sqrt_nonneg _))).mp
  rw [pairHyperbolaMean_sq hX hY, mul_pow, Real.sq_sqrt hR]
  ring

theorem integral_pairOverlapBetaTripleKernel_hyperbola (i j k l : Fin 4)
    (tv : ℝ × ℝ) (ht : tv.1 ∈ Ioo (0 : ℝ) 1) (hv : tv.2 ∈ Ioo (0 : ℝ) 1) :
    (∫ u : ℝ, pairOverlapBetaTripleKernel i j k l u tv) =
      pairOverlapBetaDensity i k tv.1 * pairOverlapBetaDensity j l tv.2 *
        pairHyperbola (pairOverlapBetaExponent i k) (pairOverlapBetaExponent j l)
          (a * Real.sqrt (tv.1*(1-tv.1)*tv.2*(1-tv.2))) := by
  simp_rw [pairOverlapBetaTripleKernel_reciprocal]
  rw [integral_const_mul, integral_reciprocal_powers_eq_pairHyperbola,
    pairHyperbolaMean_beta ht hv]
  · positivity [witness_basic.2.1, ht.1, sub_pos.mpr ht.2]
  · positivity [witness_basic.2.1, hv.1, sub_pos.mpr hv.2]

def pairOverlapBetaHyperbolaKernel (i j k l : Fin 4) (tv : ℝ × ℝ) : ℝ :=
  pairOverlapBetaDensity i k tv.1 * pairOverlapBetaDensity j l tv.2 *
    pairHyperbola (pairOverlapBetaExponent i k) (pairOverlapBetaExponent j l)
      (a * Real.sqrt (tv.1*(1-tv.1)*tv.2*(1-tv.2)))

theorem pairOverlapBetaHyperbolaKernel_ae (i j k l : Fin 4) :
    (fun tv => ∫ u : ℝ, pairOverlapBetaTripleKernel i j k l u tv) =ᵐ[
      pairOverlapBetaSquareMeasure] pairOverlapBetaHyperbolaKernel i j k l := by
  have hp : ∀ᵐ tv ∂pairOverlapBetaSquareMeasure,
      tv ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    unfold pairOverlapBetaSquareMeasure
    rw [Measure.prod_restrict]
    exact self_mem_ae_restrict (measurableSet_Ioo.prod measurableSet_Ioo)
  filter_upwards [hp] with tv htv
  exact integral_pairOverlapBetaTripleKernel_hyperbola i j k l tv htv.1 htv.2

theorem integrable_pairOverlapBetaHyperbolaKernel (i j k l : Fin 4) :
    Integrable (pairOverlapBetaHyperbolaKernel i j k l) pairOverlapBetaSquareMeasure :=
  (integrable_pairOverlapBetaTripleKernel i j k l).integral_prod_right.congr
    (pairOverlapBetaHyperbolaKernel_ae i j k l)

/-- The actual four-index monomial overlap is an exact normalized double beta
expectation of the reciprocal hyperbola integral. -/
theorem pairOverlapMonomial_eq_betaHyperbola (i j k l : Fin 4) :
    pairOverlapMonomial i j k l =
      (Real.pi / a)^2 / (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l) *
        ∫ t in Ioo (0 : ℝ) 1, ∫ v in Ioo (0 : ℝ) 1,
          pairOverlapBetaDensity i k t * pairOverlapBetaDensity j l v *
            pairHyperbola (pairOverlapBetaExponent i k) (pairOverlapBetaExponent j l)
              (a * Real.sqrt (t*(1-t)*v*(1-v))) := by
  rw [pairOverlapMonomial_eq_betaTriple,
    integral_congr_ae (pairOverlapBetaHyperbolaKernel_ae i j k l)]
  have hi := integrable_pairOverlapBetaHyperbolaKernel i j k l
  unfold pairOverlapBetaSquareMeasure at hi ⊢
  rw [integral_prod _ hi]
  unfold pairOverlapBetaHyperbolaKernel pairOverlapBetaScale
  congr 1
  ring

end UnitDistance.Witness
