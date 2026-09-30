module

public import UnitDistance.PairMassWideCertificateAstra
public import UnitDistance.PairMassDegree3SharperSummationAstra

@[expose] public section
set_option backward.privateInPublic true


/-! Unconditional sharper consequences of the checked degree-three pair-mass
certificate. Kept separate from the wide target integration module. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace UnitDistance.Witness

/-- Exact value of the rational 64-cell outward sum used by the certificate. -/
theorem pairMass_outward_sum3_exact_astra :
    (∑ i : Fin 8, ∑ j : Fin 8,
      pairMassContractionUpper3 i j * pairMassCenterPowerUpper i j) =
      (77937724053617020685714880552767926909 : ℝ) /
        2000000000000000000000000000000000000 :=
  pairMass_outward_sum3_exact

/-- Unconditional exact rational upper bound for the beta-square mass. -/
theorem pairMassBetaIntegral_le_exact_astra :
    pairMassBetaIntegral ≤
      (77937724053617020685714880552767926909 : ℝ) /
        2000000000000000000000000000000000000 :=
  pairMassBetaIntegral_le_of_degree3_contraction_bounds_exact
    pairMassCellContraction3_le_upper

/-- A compact six-decimal unconditional mass bound. -/
theorem pairMassBetaIntegral_le_38968863 :
    pairMassBetaIntegral ≤ (38968863 : ℝ) / 1000000 :=
  pairMassBetaIntegral_le_of_degree3_contraction_bounds_sharper
    pairMassCellContraction3_le_upper

end UnitDistance.Witness
