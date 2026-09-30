module

public import UnitDistance.SigmaCutArithmeticWitness
public import UnitDistance.GaloisRetainedFamily
public import UnitDistance.GaloisQuotientDescent

@[expose] public section
set_option backward.privateInPublic true


/-! Actual growing finite Galois number fields extracted from the arithmetic
cut. Every layer contains the actual retained field and the cubic detector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace UnitDistance.ArithmeticProP.SigmaCut
open GaloisQuotient ArithmeticRetained NumberField

instance actualQuotient_totallyDisconnected : TotallyDisconnectedSpace ActualQuotient :=
  ProCGroups.totallyDisconnectedSpace_quotient_closedNormal (kernel actualExtra)
    (kernel_closed actualExtra)

/-- The actual growing family, obtained from proved infinitude of the cut. -/
def family (hgen : ArithmeticPresentation) :
    Family ℚ maximalSigmaProTwo ActualQuotient (arithmeticProjection actualExtra hgen).toMonoidHom := by
  letI : Infinite ActualQuotient := infinite_of_arithmeticPresentation hgen
  exact retainedFamily (arithmeticProjection actualExtra hgen)
    (arithmeticProjection_surjective actualExtra hgen)
    retainedFieldEmbeddingMaximalSigmaProTwo (arithmeticCubic hgen)
    (arithmeticProjection_retained_kernel hgen) (arithmeticCubic_kernel hgen)

abbrev Level (hgen : ArithmeticPresentation) (j : ℕ) := (family hgen).level j

instance levelAlgebra (hgen : ArithmeticPresentation) (j : ℕ) : Algebra ℚ (Level hgen j) :=
  (Level hgen j).algebra'
instance levelFinite (hgen : ArithmeticPresentation) (j : ℕ) : Module.Finite ℚ (Level hgen j) :=
  (family hgen).finite j
instance levelGalois (hgen : ArithmeticPresentation) (j : ℕ) : IsGalois ℚ (Level hgen j) :=
  (family hgen).galois j
instance levelNumberField (hgen : ArithmeticPresentation) (j : ℕ) : NumberField (Level hgen j) :=
  NumberField.of_module_finite ℚ _

def levelEmbedding (hgen : ArithmeticPresentation) (j : ℕ) :
    Level hgen j →ₐ[ℚ] maximalSigmaProTwo := (Level hgen j).val

theorem level_kernel_fixes (hgen : ArithmeticPresentation) (j : ℕ) :
    (arithmeticProjection actualExtra hgen).toMonoidHom.ker ≤ (Level hgen j).fixingSubgroup :=
  (family hgen).kernel_fixes j

theorem level_retained_le (hgen : ArithmeticPresentation) (j : ℕ) :
    retainedFieldEmbeddingMaximalSigmaProTwo.fieldRange ≤ Level hgen j := by
  letI : Infinite ActualQuotient := infinite_of_arithmeticPresentation hgen
  exact retainedRange_le_level (arithmeticProjection actualExtra hgen)
    (arithmeticProjection_surjective actualExtra hgen)
    retainedFieldEmbeddingMaximalSigmaProTwo (arithmeticCubic hgen)
    (arithmeticProjection_retained_kernel hgen) (arithmeticCubic_kernel hgen) j

theorem level_detector_le (hgen : ArithmeticPresentation) (j : ℕ) :
    finiteQuotientField (arithmeticCubic hgen) ≤ Level hgen j := by
  letI : Infinite ActualQuotient := infinite_of_arithmeticPresentation hgen
  exact detectorField_le_level (arithmeticProjection actualExtra hgen)
    (arithmeticProjection_surjective actualExtra hgen)
    retainedFieldEmbeddingMaximalSigmaProTwo (arithmeticCubic hgen)
    (arithmeticProjection_retained_kernel hgen) (arithmeticCubic_kernel hgen) j

/-- The specified actual retained embedding into each literal layer. -/
def levelRetainedEmbedding (hgen : ArithmeticPresentation) (j : ℕ) :
    RetainedField →ₐ[ℚ] Level hgen j :=
  (IntermediateField.inclusion (level_retained_le hgen j)).comp
    retainedFieldEmbeddingMaximalSigmaProTwo.equivFieldRange.toAlgHom

@[simp] theorem levelEmbedding_retained (hgen : ArithmeticPresentation) (j : ℕ) (x : RetainedField) :
    levelEmbedding hgen j (levelRetainedEmbedding hgen j x)=
      retainedFieldEmbeddingMaximalSigmaProTwo x := rfl

instance levelAlgebraRetained (hgen : ArithmeticPresentation) (j : ℕ) :
    Algebra RetainedField (Level hgen j) := (levelRetainedEmbedding hgen j).toRingHom.toAlgebra

def toLevel (hgen : ArithmeticPresentation) (j : ℕ) : ActualQuotient →ₜ* Gal(Level hgen j/ℚ) :=
  quotientToLayer (arithmeticProjection actualExtra hgen)
    (arithmeticProjection_surjective actualExtra hgen) (Level hgen j) (level_kernel_fixes hgen j)

@[simp] theorem toLevel_arithmetic (hgen : ArithmeticPresentation) (j : ℕ) (g : SigmaGroup) :
    toLevel hgen j (arithmeticProjection actualExtra hgen g)=
      GaloisEmbedding.restriction (levelEmbedding hgen j) g :=
  quotientToLayer_apply _ _ _ _ g

theorem toLevel_surjective (hgen : ArithmeticPresentation) (j : ℕ) :
    Function.Surjective (toLevel hgen j) := quotientToLayer_surjective _ _ _ _

/-- Actual restriction to the retained field, transported to its proved group model. -/
def levelRetained (hgen : ArithmeticPresentation) (j : ℕ) :
    Gal(Level hgen j/ℚ) →ₜ* RetainedQuadratic.Q where
  toMonoidHom := sigmaRetainedModelEquiv.symm.toMonoidHom.comp
    (GaloisEmbedding.restriction (levelRetainedEmbedding hgen j)).toMonoidHom
  continuous_toFun := (continuous_of_discreteTopology : Continuous sigmaRetainedModelEquiv.symm).comp
    (GaloisEmbedding.restriction (levelRetainedEmbedding hgen j)).continuous_toFun

theorem levelRetained_surjective (hgen : ArithmeticPresentation) (j : ℕ) :
    Function.Surjective (levelRetained hgen j) :=
  sigmaRetainedModelEquiv.symm.surjective.comp
    (GaloisEmbedding.restriction_surjective (levelRetainedEmbedding hgen j))

theorem levelRetained_toLevel (hgen : ArithmeticPresentation) (j : ℕ) (q : ActualQuotient) :
    levelRetained hgen j (toLevel hgen j q)=retained actualExtra q := by
  obtain ⟨g,rfl⟩ := arithmeticProjection_surjective actualExtra hgen q
  rw [toLevel_arithmetic,arithmeticProjection_retained]
  change sigmaRetainedModelEquiv.symm
    (GaloisEmbedding.restriction (levelRetainedEmbedding hgen j)
      (GaloisEmbedding.restriction (levelEmbedding hgen j) g))=sigmaRetainedModelMap g
  rw [←GaloisEmbedding.restriction_comp]
  rfl

theorem levelRetained_comp_toLevel (hgen : ArithmeticPresentation) (j : ℕ) :
    (levelRetained hgen j).comp (toLevel hgen j)=retained actualExtra := by
  apply ContinuousMonoidHom.ext
  intro q
  exact levelRetained_toLevel hgen j q

theorem level_degree_tendsto (hgen : ArithmeticPresentation) :
    Filter.Tendsto (fun j => Module.finrank ℚ (Level hgen j)) Filter.atTop Filter.atTop :=
  (family hgen).degree_tendsto

def levelConjugation (hgen : ArithmeticPresentation) (j : ℕ) : Gal(Level hgen j/ℚ) :=
  GaloisEmbedding.restriction (levelEmbedding hgen j) sigmaComplexConjugation

def levelComplexEmbedding (hgen : ArithmeticPresentation) (j : ℕ) : Level hgen j →+* ℂ :=
  sigmaComplexEmbedding.comp (levelEmbedding hgen j).toRingHom

theorem levelConjugation_isConj (hgen : ArithmeticPresentation) (j : ℕ) :
    ComplexEmbedding.IsConj (levelComplexEmbedding hgen j) (levelConjugation hgen j) :=
  GaloisEmbedding.restriction_isConj (levelEmbedding hgen j) _ _ sigmaComplexConjugation_isConj

theorem levelConjugation_index (hgen : ArithmeticPresentation) (j : ℕ) :
    4096 ≤ (Subgroup.centralizer ({levelConjugation hgen j} : Set Gal(Level hgen j/ℚ))).index := by
  let π := finiteQuotientOnLayer (arithmeticCubic hgen) (Level hgen j) (level_detector_le hgen j)
  have hp := GaloisConjugation.centralizer_index_le_of_surjective π
    (finiteQuotientOnLayer_surjective _ _ (arithmeticCubic_surjective hgen)
      (level_detector_le hgen j)) (levelConjugation hgen j)
  have he : π (levelConjugation hgen j)=arithmeticCubic hgen sigmaComplexConjugation :=
    finiteQuotientOnLayer_restriction _ _ _ _
  rw [he] at hp
  exact (arithmeticCubic_conjugacy_index hgen).trans hp

end UnitDistance.ArithmeticProP.SigmaCut
