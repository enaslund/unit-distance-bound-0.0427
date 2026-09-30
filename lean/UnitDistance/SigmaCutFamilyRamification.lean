module

public import UnitDistance.SigmaCutFamily
public import UnitDistance.SigmaCutFiniteArithmetic
public import UnitDistance.RetainedSelectedIndices
public import UnitDistance.RelativeUnramifiedSigma
public import UnitDistance.SigmaFiniteRamification

@[expose] public section
set_option backward.privateInPublic true


/-! Exact ideal indices and finite unramifiedness over M for every actual
layer of the constructed infinite arithmetic cut. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open NumberField
namespace UnitDistance.ArithmeticProP.SigmaCut
open NumberFieldAnalysis ArithmeticRetained

/-- Exact ramification and residue data in each genuine growing field. -/
theorem level_ramification_residue (hgen : ArithmeticPresentation) (j : ℕ) (a : Fin 11) :
    (rationalPrimeIdeal (Witness.primes a)).ramificationIdxIn (𝓞 (Level hgen j))=Witness.ramification a ∧
    (rationalPrimeIdeal (Witness.primes a)).inertiaDegIn (𝓞 (Level hgen j))=Witness.residueDegree a := by
  apply selected_ramification_residue hgen (Level hgen j) (levelEmbedding hgen j)
    (toLevel hgen j) (levelRetained hgen j).toMonoidHom
  · exact congrArg ContinuousMonoidHom.toMonoidHom (levelRetained_comp_toLevel hgen j)
  · exact toLevel_arithmetic hgen j

/-- All growing fields are genuinely unramified over the actual retained field. -/
theorem level_finiteUnramified_retained (hgen : ArithmeticPresentation) (j : ℕ) :
    FiniteUnramified RetainedField (Level hgen j) := by
  apply finiteUnramified_of_sigma_ramificationIdxIn_eq RetainedField (Level hgen j)
    (unramifiedAway_of_embedding_maximalSigma RetainedField retainedFieldEmbeddingMaximalSigmaProTwo)
    (unramifiedAway_of_embedding_maximalSigma (Level hgen j) (levelEmbedding hgen j))
  intro p hp
  simp only [sigmaRationalPrimes,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl
  · exact (level_ramification_residue hgen j 0).1.trans (retained_selected_ramification hgen 0).symm
  · exact (level_ramification_residue hgen j 1).1.trans (retained_selected_ramification hgen 1).symm
  · exact (level_ramification_residue hgen j 2).1.trans (retained_selected_ramification hgen 2).symm
  · exact (level_ramification_residue hgen j 3).1.trans (retained_selected_ramification hgen 3).symm
  · exact (level_ramification_residue hgen j 4).1.trans (retained_selected_ramification hgen 4).symm
  · exact (level_ramification_residue hgen j 5).1.trans (retained_selected_ramification hgen 5).symm

end UnitDistance.ArithmeticProP.SigmaCut
