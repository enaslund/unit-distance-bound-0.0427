module

public import UnitDistance.PairMassDegree3Data
public import UnitDistance.PairMassEndpointCertificate

@[expose] public section
set_option backward.privateInPublic true


/-! Directed endpoint contraction of the exact degree-three coefficients. -/
noncomputable section
set_option maxHeartbeats 0
open scoped BigOperators
namespace UnitDistance.Witness

def pairMassEndpointIndex (i : Fin 8) (s : Fin 2) : Fin 9 :=
  ⟨(i:ℕ)+(s:ℕ), by omega⟩

def pairMassContractionTermUpper3 (i j : Fin 8) (s t : Fin 2) : ℝ :=
  let c : ℝ := pairMassContractionCoefficient3 i j s t
  if c < 0 then
    c * pairMassEndpointLower (pairMassEndpointIndex i s) *
      pairMassEndpointLower (pairMassEndpointIndex j t)
  else
    c * pairMassEndpointUpper (pairMassEndpointIndex i s) *
      pairMassEndpointUpper (pairMassEndpointIndex j t)

theorem pairMassContractionTerm_le_upper3 (i j : Fin 8) (s t : Fin 2) :
    (pairMassContractionCoefficient3 i j s t:ℝ) *
      pairMassEndpointRoot ((i:ℕ)+(s:ℕ)) *
      pairMassEndpointRoot ((j:ℕ)+(t:ℕ)) ≤ pairMassContractionTermUpper3 i j s t := by
  have hloi := pairMassEndpointLower_le (pairMassEndpointIndex i s)
  have hloj := pairMassEndpointLower_le (pairMassEndpointIndex j t)
  have hupi := pairMassEndpoint_le_Upper (pairMassEndpointIndex i s)
  have hupj := pairMassEndpoint_le_Upper (pairMassEndpointIndex j t)
  have hli := pairMassEndpointLower_nonneg (pairMassEndpointIndex i s)
  have hlj := pairMassEndpointLower_nonneg (pairMassEndpointIndex j t)
  have hui := pairMassEndpointUpper_nonneg (pairMassEndpointIndex i s)
  have hx : 0 ≤ pairMassEndpointRoot ((i:ℕ)+(s:ℕ)) := by
    unfold pairMassEndpointRoot
    positivity
  have hy : 0 ≤ pairMassEndpointRoot ((j:ℕ)+(t:ℕ)) := by
    unfold pairMassEndpointRoot
    positivity
  unfold pairMassContractionTermUpper3
  dsimp only
  split_ifs with hc
  · have hprod := mul_le_mul hloi hloj hlj hx
    have h := mul_le_mul_of_nonpos_left hprod hc.le
    simpa only [pairMassEndpointIndex, mul_assoc] using h
  · have hprod := mul_le_mul hupi hupj hy hui
    have h := mul_le_mul_of_nonneg_left hprod (le_of_not_gt hc)
    simpa only [pairMassEndpointIndex, mul_assoc] using h

theorem pairMassContractionRounded_le_upper3 (i j : Fin 8) :
    (∑ s : Fin 2, ∑ t : Fin 2, pairMassContractionTermUpper3 i j s t) ≤
      pairMassContractionUpper3 i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pairMassContractionTermUpper3, pairMassContractionCoefficient3,
      pairMassEndpointIndex, pairMassEndpointLower, pairMassEndpointUpper,
      pairMassContractionUpper3, Fin.sum_univ_succ]

theorem pairMassCellContraction3_le_upper_of_expansion (i j : Fin 8)
    (h : pairMassCellContraction3 i j =
      ∑ s : Fin 2, ∑ t : Fin 2, (pairMassContractionCoefficient3 i j s t:ℝ) *
        pairMassEndpointRoot ((i:ℕ)+(s:ℕ)) * pairMassEndpointRoot ((j:ℕ)+(t:ℕ))) :
    pairMassCellContraction3 i j ≤ pairMassContractionUpper3 i j := by
  rw [h]
  exact (Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ =>
    pairMassContractionTerm_le_upper3 i j s t).trans
      (pairMassContractionRounded_le_upper3 i j)

end UnitDistance.Witness
