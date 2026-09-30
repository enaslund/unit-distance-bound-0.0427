module

public import UnitDistance.SigmaCutFamily
public import UnitDistance.SigmaFinitePrimeImages
public import UnitDistance.SigmaCutAbsoluteGenus
public import UnitDistance.WitnessPrimePairs

@[expose] public section
set_option backward.privateInPublic true


/-! Actual complex conjugation moves every prime of every selected norm in
each of the constructed growing arithmetic fields. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace UnitDistance.ArithmeticProP.SigmaCut
open PrimeCompletion NumberFieldAnalysis NumberField

/-- The retained label of actual restriction agrees with the ambient label. -/
theorem levelRetained_restriction (hgen : ArithmeticPresentation) (j : ℕ) (g : SigmaGroup) :
    levelRetained hgen j (GaloisEmbedding.restriction (levelEmbedding hgen j) g)=
      sigmaRetainedModelMap g := by
  rw [←toLevel_arithmetic,levelRetained_toLevel,arithmeticProjection_retained]

/-- Prime freedom follows from the proved full decomposition-group genus
exclusion, for all eleven literal prime norms and every actual layer. -/
theorem level_prime_moved (hgen : ArithmeticPresentation) (j : ℕ) (a : Fin 11)
    (P : PrimeNormFiber (Level hgen j) (Witness.primeNorm a)) :
    Ideal.map (RingOfIntegers.mapRingHom (levelConjugation hgen j).toRingHom)
      P.1.asIdeal≠P.1.asIdeal := by
  let π := (ClassTwo.GroupModel.baseHom RetainedQuadratic.cocycle).comp
    (levelRetained hgen j).toMonoidHom
  apply prime_moved_of_absolute_genus_exclusion
    (M := Level hgen j) (p := selectedPrime a)
    (j := sigmaAbsoluteEmbedding (Level hgen j) (levelEmbedding hgen j)) π
    (levelConjugation hgen j) ?_ (Witness.residueDegree a) (Witness.residueDegree_pos a) P
  intro d hd
  change Multiplicative.ofAdd (levelRetained hgen j
      (decompositionRestriction (selectedPrime a) (Level hgen j)
        (sigmaAbsoluteEmbedding (Level hgen j) (levelEmbedding hgen j)) d)).base=
    Multiplicative.ofAdd (levelRetained hgen j (levelConjugation hgen j)).base at hd
  rw [←sigmaRestriction_decomposition,levelRetained_restriction] at hd
  change Multiplicative.ofAdd (sigmaRetainedModelMap
    (SigmaUnramified.decompositionMap (selectedPrime a) d)).base=
      Multiplicative.ofAdd (levelRetained hgen j
        (GaloisEmbedding.restriction (levelEmbedding hgen j) sigmaComplexConjugation)).base at hd
  rw [levelRetained_restriction,complexConjugation_retained_base] at hd
  exact selected_absolute_genus_exclusion actualExtra hgen a d
    (Multiplicative.ofAdd.injective hd)

end UnitDistance.ArithmeticProP.SigmaCut
