module

public import UnitDistance.PairOverlapRemainderSum
public import UnitDistance.PairOverlapLeadingBetaIntegral
public import UnitDistance.PairOverlapLeadingNumerics

@[expose] public section
set_option backward.privateInPublic true


/-! Assembly of the leading beta integral and its rigorously bounded remainder. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped BigOperators

namespace UnitDistance.Witness

theorem integral_pairOverlapBetaLeadingKernel (i j k l : Fin 4) :
    (∫ tv : ℝ × ℝ, pairOverlapBetaLeadingKernel i j k l tv
      ∂pairOverlapBetaSquareMeasure) = pairOverlapLeadingMean i j k l := by
  have h := integrable_pairOverlapBetaLeadingKernel i j k l
  unfold pairOverlapBetaSquareMeasure at h ⊢
  rw [integral_prod _ h]
  exact integral_pairOverlapBetaDensity_leading i j k l

theorem integral_pairOverlapBetaHyperbolaKernel_decomposition (i j k l : Fin 4) :
    (∫ tv : ℝ × ℝ, pairOverlapBetaHyperbolaKernel i j k l tv
      ∂pairOverlapBetaSquareMeasure) =
      pairOverlapLeadingMean i j k l +
        (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l) *
          pairOverlapRemainderMean i j k l := by
  let A := pairOverlapBetaExponent i k
  let B := pairOverlapBetaExponent j l
  have hA : 0 < A := pairOverlapBetaExponent_pos i k
  have hB : 0 < B := pairOverlapBetaExponent_pos j l
  have hactual := integrable_pairOverlapBetaHyperbolaKernel i j k l
  have hleading := integrable_pairOverlapBetaLeadingKernel i j k l
  have hrem := integrable_pairOverlapBetaNormalizedRemainderKernel i j k l
  have hp : ∀ᵐ tv ∂pairOverlapBetaSquareMeasure,
      tv ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    unfold pairOverlapBetaSquareMeasure
    rw [Measure.prod_restrict]
    exact self_mem_ae_restrict (measurableSet_Ioo.prod measurableSet_Ioo)
  have hdecomp : pairOverlapBetaHyperbolaKernel i j k l =ᵐ[
      pairOverlapBetaSquareMeasure]
      fun tv => pairOverlapBetaLeadingKernel i j k l tv +
        (A * B) * pairOverlapBetaNormalizedRemainderKernel i j k l tv := by
    filter_upwards [hp] with tv htv
    have hb := pairOverlap_betaScale_pos_le_one htv.1 htv.2
    dsimp only [A, B]
    unfold pairOverlapBetaHyperbolaKernel pairOverlapBetaLeadingKernel
      pairOverlapBetaNormalizedRemainderKernel
    have hA' := pairOverlapBetaExponent_pos i k
    have hB' := pairOverlapBetaExponent_pos j l
    rw [pairHyperbola_eq_leading_add_remainder hA' hB' hb.1 hb.2]
    field_simp [hA'.ne', hB'.ne']
  calc
    (∫ tv : ℝ × ℝ, pairOverlapBetaHyperbolaKernel i j k l tv
        ∂pairOverlapBetaSquareMeasure) =
        ∫ tv : ℝ × ℝ, (pairOverlapBetaLeadingKernel i j k l tv +
          (A * B) * pairOverlapBetaNormalizedRemainderKernel i j k l tv)
            ∂pairOverlapBetaSquareMeasure := integral_congr_ae hdecomp
    _ = (∫ tv : ℝ × ℝ, pairOverlapBetaLeadingKernel i j k l tv
          ∂pairOverlapBetaSquareMeasure) +
        ∫ tv : ℝ × ℝ, (A * B) *
          pairOverlapBetaNormalizedRemainderKernel i j k l tv
            ∂pairOverlapBetaSquareMeasure :=
      integral_add hleading (hrem.const_mul (A * B))
    _ = pairOverlapLeadingMean i j k l +
        (A * B) * pairOverlapRemainderMean i j k l := by
      rw [integral_pairOverlapBetaLeadingKernel, integral_const_mul]
      rfl
    _ = pairOverlapLeadingMean i j k l +
        (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l) *
          pairOverlapRemainderMean i j k l := by rfl

theorem pairOverlapMonomial_eq_leading_add_remainder (i j k l : Fin 4) :
    pairOverlapMonomial i j k l = pairArchScale *
      (pairOverlapLeadingMean i j k l /
          (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l) +
        pairOverlapRemainderMean i j k l) := by
  have hA := pairOverlapBetaExponent_pos i k
  have hB := pairOverlapBetaExponent_pos j l
  have hactual := integrable_pairOverlapBetaHyperbolaKernel i j k l
  rw [pairOverlapMonomial_eq_betaHyperbola]
  have hiterated :
      (∫ t in Ioo (0 : ℝ) 1, ∫ v in Ioo (0 : ℝ) 1,
        pairOverlapBetaDensity i k t * pairOverlapBetaDensity j l v *
          pairHyperbola (pairOverlapBetaExponent i k) (pairOverlapBetaExponent j l)
            (a * Real.sqrt (t*(1-t)*v*(1-v)))) =
      ∫ tv : ℝ × ℝ, pairOverlapBetaHyperbolaKernel i j k l tv
        ∂pairOverlapBetaSquareMeasure := by
    unfold pairOverlapBetaSquareMeasure at hactual ⊢
    rw [integral_prod _ hactual]
    rfl
  rw [hiterated, integral_pairOverlapBetaHyperbolaKernel_decomposition]
  unfold pairArchScale
  field_simp [witness_basic.2.1.ne', hA.ne', hB.ne']

end UnitDistance.Witness
