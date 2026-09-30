module

public import UnitDistance.PairOverlapBetaDensity

@[expose] public section
set_option backward.privateInPublic true


/-! Fubini for the exact beta representation of each monomial overlap. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace UnitDistance.Witness

def pairOverlapBetaSquareMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))

instance : SFinite pairOverlapBetaSquareMeasure := by
  unfold pairOverlapBetaSquareMeasure
  infer_instance

def pairOverlapBetaTripleKernel (i j k l : Fin 4) (u : ℝ) (tv : ℝ × ℝ) : ℝ :=
  pairOverlapBetaShiftKernel i k (Real.exp u : ℂ) tv.1 *
    pairOverlapBetaShiftKernel j l (Real.exp (-u) : ℂ) tv.2

def pairOverlapBetaScale (i j k l : Fin 4) : ℝ :=
  (Real.pi / (a * pairOverlapBetaExponent i k)) *
    (Real.pi / (a * pairOverlapBetaExponent j l))

theorem pairOverlapBetaScale_pos (i j k l : Fin 4) :
    0 < pairOverlapBetaScale i j k l := by
  unfold pairOverlapBetaScale
  positivity [witness_basic.2.1, pairOverlapBetaExponent_pos i k, pairOverlapBetaExponent_pos j l]

theorem integrable_pairOverlapBetaTripleKernel_slice (i j k l : Fin 4) (u : ℝ) :
    Integrable (pairOverlapBetaTripleKernel i j k l u) pairOverlapBetaSquareMeasure :=
  (integrableOn_pairOverlapBetaShiftKernel i k (Real.exp u : ℂ)).mul_prod
    (integrableOn_pairOverlapBetaShiftKernel j l (Real.exp (-u) : ℂ))

theorem pairOverlapBetaTripleKernel_nonneg_ae (i j k l : Fin 4) (u : ℝ) :
    0 ≤ᵐ[pairOverlapBetaSquareMeasure] pairOverlapBetaTripleKernel i j k l u := by
  have hp : ∀ᵐ tv ∂pairOverlapBetaSquareMeasure,
      tv ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    unfold pairOverlapBetaSquareMeasure
    rw [Measure.prod_restrict]
    exact self_mem_ae_restrict (measurableSet_Ioo.prod measurableSet_Ioo)
  filter_upwards [hp] with tv htv
  exact mul_nonneg (pairOverlapBetaShiftKernel_nonneg i k _ htv.1)
    (pairOverlapBetaShiftKernel_nonneg j l _ htv.2)

theorem integral_pairOverlapBetaTripleKernel_slice (i j k l : Fin 4) (u : ℝ) :
    (∫ tv, pairOverlapBetaTripleKernel i j k l u tv ∂pairOverlapBetaSquareMeasure) =
      (pairOverlapBetaScale i j k l)⁻¹ *
        (pairOverlapCoordinateConvolution i k (Real.exp u : ℂ) *
          pairOverlapCoordinateConvolution j l (Real.exp (-u) : ℂ)) := by
  unfold pairOverlapBetaTripleKernel pairOverlapBetaSquareMeasure
  rw [integral_prod_mul, pairOverlapCoordinateConvolution_beta_density,
    pairOverlapCoordinateConvolution_beta_density]
  unfold pairOverlapBetaScale
  have ha := witness_basic.2.1.ne'
  have hA := (pairOverlapBetaExponent_pos i k).ne'
  have hB := (pairOverlapBetaExponent_pos j l).ne'
  field_simp

theorem integrable_pairOverlapCoordinateConvolution_product (i j k l : Fin 4) :
    Integrable (fun u : ℝ =>
      pairOverlapCoordinateConvolution i k (Real.exp u : ℂ) *
        pairOverlapCoordinateConvolution j l (Real.exp (-u) : ℂ)) := by
  have hi := (integrable_pairOverlapMonomialIntegrand i j k l).integral_prod_left
  apply hi.congr
  filter_upwards with u
  exact pairOverlapMonomialIntegrand_spatial i j k l u

theorem integrable_pairOverlapBetaTripleKernel (i j k l : Fin 4) :
    Integrable (Function.uncurry (pairOverlapBetaTripleKernel i j k l))
      (volume.prod pairOverlapBetaSquareMeasure) := by
  have hm : Measurable (Function.uncurry (pairOverlapBetaTripleKernel i j k l)) := by
    unfold pairOverlapBetaTripleKernel pairOverlapBetaShiftKernel pairOverlapBetaDensity
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (integrable_pairOverlapBetaTripleKernel_slice i j k l)
  · have hi := (integrable_pairOverlapCoordinateConvolution_product i j k l).const_mul
      (pairOverlapBetaScale i j k l)⁻¹
    apply hi.congr
    filter_upwards with u
    rw [← integral_pairOverlapBetaTripleKernel_slice]
    apply integral_congr_ae
    filter_upwards [pairOverlapBetaTripleKernel_nonneg_ae i j k l u] with tv htv
    exact (Real.norm_of_nonneg htv).symm

/-- Exact Fubini exchange from logarithmic displacement to the two beta
variables, with integrability inherited from the actual spatial overlap. -/
theorem pairOverlapMonomial_eq_betaTriple (i j k l : Fin 4) :
    pairOverlapMonomial i j k l = pairOverlapBetaScale i j k l *
      ∫ tv, (∫ u : ℝ, pairOverlapBetaTripleKernel i j k l u tv)
        ∂pairOverlapBetaSquareMeasure := by
  rw [← integral_integral_swap (integrable_pairOverlapBetaTripleKernel i j k l)]
  simp_rw [integral_pairOverlapBetaTripleKernel_slice]
  rw [integral_const_mul, ← pairOverlapMonomial_eq_convolutions]
  rw [← mul_assoc, mul_inv_cancel₀ (pairOverlapBetaScale_pos i j k l).ne', one_mul]

end UnitDistance.Witness
