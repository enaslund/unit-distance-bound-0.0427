module

public import UnitDistance.PairOverlapRemainderAssembly
public import UnitDistance.PairFunctionalCoarseCertificate

@[expose] public section
set_option backward.privateInPublic true


/-! The unconditional coarse lower bound for the literal pair-overlap integral. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace UnitDistance.Witness

theorem pairOverlap_eq_archScale_mul_leading_add_remainder :
    pairOverlap = pairArchScale *
      ((pairOverlapB0 : ℝ) * (Real.log (1/a) + pairOverlapStudentConstant) +
        (pairOverlapV0 : ℝ) + pairOverlapRemainderContribution) := by
  rw [pairOverlap_eq_sum_monomialOverlaps]
  simp_rw [pairOverlapMonomial_eq_leading_add_remainder]
  rw [← sum_pairOverlapLeadingMean_collected]
  unfold pairOverlapRemainderContribution pairOverlapCoefficientProduct
  calc
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
      ((pairOverlapPowerCoefficient i j : ℝ) *
        (pairOverlapPowerCoefficient k l : ℝ)) *
          (pairArchScale *
            (pairOverlapLeadingMean i j k l /
                (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l) +
              pairOverlapRemainderMean i j k l))) =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        pairArchScale *
          (((pairOverlapPowerCoefficient i j : ℝ) *
              (pairOverlapPowerCoefficient k l : ℝ)) *
                (pairOverlapLeadingMean i j k l /
                  (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l)) +
            ((pairOverlapPowerCoefficient i j : ℝ) *
              (pairOverlapPowerCoefficient k l : ℝ)) *
                pairOverlapRemainderMean i j k l) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        ring
    _ = pairArchScale *
      (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        (((pairOverlapPowerCoefficient i j : ℝ) *
            (pairOverlapPowerCoefficient k l : ℝ)) *
              (pairOverlapLeadingMean i j k l /
                (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l)) +
          ((pairOverlapPowerCoefficient i j : ℝ) *
            (pairOverlapPowerCoefficient k l : ℝ)) *
              pairOverlapRemainderMean i j k l)) := by
        simp only [Finset.mul_sum]
    _ = pairArchScale *
      ((∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        ((pairOverlapPowerCoefficient i j : ℝ) *
          (pairOverlapPowerCoefficient k l : ℝ)) *
            (pairOverlapLeadingMean i j k l /
              (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l))) +
       (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        ((pairOverlapPowerCoefficient i j : ℝ) *
          (pairOverlapPowerCoefficient k l : ℝ)) *
            pairOverlapRemainderMean i j k l)) := by
        simp only [Finset.sum_add_distrib]

/-- The overlap endpoint used by the coarse pair-functional certificate follows
from the literal integral, with no numerical oracle. -/
theorem pairOverlap_coarse_lower :
    coarsePairOverlapLower * pairArchScale ≤ pairOverlap := by
  have hlead := pairOverlapLeadingNumerical_lower
  have hrem := pairOverlapRemainderContribution_lower
  have htotal : coarsePairOverlapLower ≤
      (pairOverlapB0 : ℝ) * (Real.log (1/a) + pairOverlapStudentConstant) +
        (pairOverlapV0 : ℝ) + pairOverlapRemainderContribution := by
    norm_num [coarsePairOverlapLower] at hlead hrem ⊢
    linarith
  rw [pairOverlap_eq_archScale_mul_leading_add_remainder]
  calc
    coarsePairOverlapLower * pairArchScale =
        pairArchScale * coarsePairOverlapLower := mul_comm _ _
    _ ≤ pairArchScale *
        ((pairOverlapB0 : ℝ) * (Real.log (1/a) + pairOverlapStudentConstant) +
          (pairOverlapV0 : ℝ) + pairOverlapRemainderContribution) :=
      mul_le_mul_of_nonneg_left htotal pairArchScale_pos.le

end UnitDistance.Witness
