module

public import UnitDistance.PairOverlapRemainderBound

@[expose] public section
set_option backward.privateInPublic true


/-!
# Signed finite sum of the overlap remainders

The beta-averaged remainder of each monomial is nonnegative and at most
`1.47e-10`.  This file keeps the signs of the power-basis coefficients and
bounds their total adverse contribution by `3e-7`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace UnitDistance.Witness

def pairOverlapCoefficientProduct (i j k l : Fin 4) : ℝ :=
  (pairOverlapPowerCoefficient i j : ℝ) *
    (pairOverlapPowerCoefficient k l : ℝ)

def pairOverlapNegativeCoefficientSum : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
    min (pairOverlapCoefficientProduct i j k l) 0

def pairOverlapRemainderContribution : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
    pairOverlapCoefficientProduct i j k l * pairOverlapRemainderMean i j k l

theorem pairOverlapNegativeCoefficientSum_lower :
    (-2000 : ℝ) ≤ pairOverlapNegativeCoefficientSum := by
  norm_num [pairOverlapNegativeCoefficientSum, pairOverlapCoefficientProduct,
    pairOverlapPowerCoefficient, Fin.sum_univ_succ, min_def]

private theorem pairOverlapRemainderTerm_lower (i j k l : Fin 4) :
    min (pairOverlapCoefficientProduct i j k l) 0 * ((147 : ℝ) / 10^12) ≤
      pairOverlapCoefficientProduct i j k l * pairOverlapRemainderMean i j k l := by
  obtain ⟨hr0, hrε⟩ := pairOverlapRemainderMean_nonneg_le i j k l
  by_cases hc : 0 ≤ pairOverlapCoefficientProduct i j k l
  · rw [min_eq_right hc]
    simpa only [zero_mul] using mul_nonneg hc hr0
  · have hc' : pairOverlapCoefficientProduct i j k l ≤ 0 := le_of_not_ge hc
    rw [min_eq_left hc']
    exact mul_le_mul_of_nonpos_left hrε hc'

/-- The signed sum of all 256 normalized monomial remainders loses less than
`3e-7` from the leading overlap estimate. -/
theorem pairOverlapRemainderContribution_lower :
    (-(3 : ℝ) / 10^7) ≤ pairOverlapRemainderContribution := by
  let ε : ℝ := 147 / 10^12
  have hε : 0 ≤ ε := by norm_num [ε]
  have hcoeff : (-2000 : ℝ) * ε ≤ pairOverlapNegativeCoefficientSum * ε :=
    mul_le_mul_of_nonneg_right pairOverlapNegativeCoefficientSum_lower hε
  have hsum : pairOverlapNegativeCoefficientSum * ε ≤
      pairOverlapRemainderContribution := by
    unfold pairOverlapNegativeCoefficientSum pairOverlapRemainderContribution
    dsimp only [ε]
    simp_rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
        pairOverlapRemainderTerm_lower i j k l
  calc
    (-(3 : ℝ) / 10^7) ≤ (-2000 : ℝ) * ε := by norm_num [ε]
    _ ≤ pairOverlapNegativeCoefficientSum * ε := hcoeff
    _ ≤ pairOverlapRemainderContribution := hsum

end UnitDistance.Witness
