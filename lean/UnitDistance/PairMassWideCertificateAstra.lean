module

public import UnitDistance.PairMassDegree3DenseCertificate
public import UnitDistance.PairMassDegree3EndpointContractionCertificate
public import UnitDistance.PairMassDegree3SummationCertificate
public import UnitDistance.PairFunctionalWideCertificate

@[expose] public section
set_option backward.privateInPublic true


/-! The literal beta-square mass bound from the degree-three finite certificate. -/
noncomputable section
set_option autoImplicit false
namespace UnitDistance.Witness

theorem pairMassCellContraction3_le_upper (i j : Fin 8) :
    pairMassCellContraction3 i j ≤ pairMassContractionUpper3 i j :=
  pairMassCellContraction3_le_upper_of_expansion i j (pairMassCellContraction3_expansion i j)

theorem pairMassBetaIntegral_le_wide : pairMassBetaIntegral ≤ widePairMassUpper :=
  pairMassBetaIntegral_le_of_degree3_contraction_bounds pairMassCellContraction3_le_upper

end UnitDistance.Witness
