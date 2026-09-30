module

public import UnitDistance.SigmaCutFamilyRamification
public import UnitDistance.SigmaCutFamilyPrimeFreedom
public import UnitDistance.SIntegerWitnessInfiniteQuotient

@[expose] public section
set_option backward.privateInPublic true


/-! The actual arithmetic construction implies the full planar target under
only the three independently stated finite numerical inequalities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace UnitDistance.ArithmeticProP.SigmaCut
open NumberField NumberFieldAnalysis Witness SIntegerCRT ArithmeticRetained Filter

/-- Terminal arithmetic and geometric result; no field-family or local
arithmetic hypothesis remains. -/
theorem target_of_arithmeticPresentation (hgen : ArithmeticPresentation)
    (hpair : (1379635324335 : ℝ)/10^12 ≤ JPair)
    (hdiscM : Real.log (rootDiscriminant RetainedField) ≤ logRD)
    (hfinite : Real.log (dedekindZeta RetainedField ((1+(1/12000:ℝ):ℝ):ℂ)).re /
        (524288 : ℝ) + (1/12000:ℝ)*
          ((logRD-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4-
            (logDeriv (dedekindZeta RetainedField) 2).re/(524288 : ℝ)) < ceiling) :
    Target := by
  letI : Infinite ActualQuotient := infinite_of_arithmeticPresentation hgen
  apply target_of_infinite_retained_quotient (arithmeticProjection actualExtra hgen)
    (arithmeticProjection_surjective actualExtra hgen)
    retainedFieldEmbeddingMaximalSigmaProTwo (arithmeticCubic hgen)
    (arithmeticProjection_retained_kernel hgen) (arithmeticCubic_kernel hgen)
    (arithmeticCubic_surjective hgen) sigmaComplexEmbedding sigmaComplexConjugation
    sigmaComplexConjugation_isConj (arithmeticCubic_conjugacy_index hgen)
    ?_ ?_ ?_ ?_ hpair hdiscM hfinite
  · exact Eventually.of_forall (level_finiteUnramified_retained hgen)
  · exact Eventually.of_forall fun j a => (level_ramification_residue hgen j a).1
  · exact Eventually.of_forall fun j a => (level_ramification_residue hgen j a).2
  · exact Eventually.of_forall fun j a P => level_prime_moved hgen j a P

end UnitDistance.ArithmeticProP.SigmaCut

#print axioms UnitDistance.ArithmeticProP.SigmaCut.target_of_arithmeticPresentation
