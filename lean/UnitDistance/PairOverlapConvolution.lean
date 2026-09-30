module

public import UnitDistance.PairOverlapHyperbola

@[expose] public section
set_option backward.privateInPublic true


/-!
# Separating the two complex coordinates in each monomial overlap

The exact power-basis expansion has four finite indices.  For fixed indices,
Fubini separates the two complex coordinates, leaving the product of two
one-coordinate Student convolutions integrated over logarithmic displacement.
-/

noncomputable section

open MeasureTheory

namespace UnitDistance.Witness

def pairOverlapCoordinateConvolution (i k : Fin 4) (h : ℂ) : ℝ :=
  ∫ z : ℂ, studentCoordinate z ^ (s + (i : ℕ)) *
    studentCoordinate (z + h) ^ (s + (k : ℕ))

theorem pairOverlapMonomialIntegrand_spatial (i j k l : Fin 4) (u : ℝ) :
    (∫ z : ℂ × ℂ, pairOverlapMonomialIntegrand i j k l (u, z)) =
      pairOverlapCoordinateConvolution i k (Real.exp u : ℂ) *
        pairOverlapCoordinateConvolution j l (Real.exp (-u) : ℂ) := by
  rw [pairOverlapCoordinateConvolution, pairOverlapCoordinateConvolution]
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards with z
  unfold pairOverlapMonomialIntegrand pairOverlapMonomialProfile reciprocalPairStep
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- Exact reduction of a four-index monomial overlap to two ordinary complex
Student convolutions. -/
theorem pairOverlapMonomial_eq_convolutions (i j k l : Fin 4) :
    pairOverlapMonomial i j k l =
      ∫ u : ℝ,
        pairOverlapCoordinateConvolution i k (Real.exp u : ℂ) *
          pairOverlapCoordinateConvolution j l (Real.exp (-u) : ℂ) := by
  unfold pairOverlapMonomial
  calc
    (∫ w : ℝ × (ℂ × ℂ), pairOverlapMonomialIntegrand i j k l w) =
        ∫ u : ℝ, ∫ z : ℂ × ℂ,
          pairOverlapMonomialIntegrand i j k l (u, z) :=
      integral_prod _ (integrable_pairOverlapMonomialIntegrand i j k l)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      exact pairOverlapMonomialIntegrand_spatial i j k l u

/-- The literal witness overlap is now a finite contraction of separated
one-coordinate convolutions. -/
theorem pairOverlap_eq_sum_convolutions :
    pairOverlap =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        ((pairOverlapPowerCoefficient i j : ℝ) *
          (pairOverlapPowerCoefficient k l : ℝ)) *
          (∫ u : ℝ,
            pairOverlapCoordinateConvolution i k (Real.exp u : ℂ) *
              pairOverlapCoordinateConvolution j l (Real.exp (-u) : ℂ)) := by
  rw [pairOverlap_eq_sum_monomialOverlaps]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [pairOverlapMonomial_eq_convolutions]

end UnitDistance.Witness
