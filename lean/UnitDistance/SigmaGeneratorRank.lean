module

public import UnitDistance.SigmaQuadraticClassification
public import UnitDistance.ArithmeticGenusFrattini

@[expose] public section
set_option backward.privateInPublic true


/-! The actual maximal pro-two extension unramified outside the six finite
primes has seven generators, and the actual genus field is its Frattini field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.ProP
open ProCGroups.Generation ProCGroups.FiniteGeneration

theorem maximalSigmaProTwo_frattini :
    closedPowerCommutator 2 Gal(maximalSigmaProTwo/ℚ) =
      genusInMaximal.fixingSubgroup := by
  exact ArithmeticGenusFrattini.frattini_eq_genusFixing
    maximalSigmaProTwo_hasPGroupOpenNormalBasis
    genusInMaximal genusInMaximalEquiv indexTwo_fixedField_le_genusInMaximal

theorem maximalSigmaProTwo_generatorRank :
    TopologicallyGeneratedByAtMost 7 Gal(maximalSigmaProTwo/ℚ) ∧
      topologicalGeneratorRank Gal(maximalSigmaProTwo/ℚ) = 7 := by
  exact ArithmeticGenusFrattini.generatorRank_seven
    maximalSigmaProTwo_hasPGroupOpenNormalBasis
    genusInMaximal genusInMaximalEquiv indexTwo_fixedField_le_genusInMaximal

end UnitDistance.ArithmeticProP
