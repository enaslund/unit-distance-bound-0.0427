module

public import UnitDistance.ArithmeticRetainedRoots
public import UnitDistance.ImaginarySevenUnramified
public import UnitDistance.RelativeArithmeticAmplitude

@[expose] public section
set_option backward.privateInPublic true


/-! Actual arithmetic of conjugation-fixed fields above the retained field. -/
noncomputable section
open NumberField NumberField.ComplexEmbedding
namespace UnitDistance.GaloisConjugation
open NumberFieldAnalysis ArithmeticRetained
variable {K : Type} [Field K] [NumberField K] [IsGalois ℚ K]
  [Algebra RetainedField K]
variable (φ : K →+* ℂ) (c : Gal(K/ℚ)) (hc : IsConj φ c) (hc1 : c ≠ 1)

/-- The same actual conjugation, now viewed over its actual fixed field. -/
def fixedAutomorphism : K ≃ₐ[fixedField K c] K :=
  { c.toRingEquiv with
    commutes' := fun x => generator_fixes c x }

include hc1 in
theorem fixedAutomorphism_ne_one : fixedAutomorphism c ≠ 1 := by
  intro he
  apply hc1
  ext x
  exact congrArg (fun e : K ≃ₐ[fixedField K c] K => e x) he

include φ hc hc1 in
/-- The fixed field is actually quadratic below K. -/
theorem fixedFieldQuadratic : Algebra.IsQuadraticExtension (fixedField K c) K :=
  ⟨relativeDegree_eq_two φ c hc hc1⟩

/-- The displayed retained imaginary unit excludes every real place. -/
theorem totallyComplex_of_retained : IsTotallyComplex K := by
  refine ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mp ?_⟩
  intro hw
  exact not_isReal_of_sqrt_neg_one w.embedding (imaginaryUnitIn K) (imaginaryUnitIn_sq K)
    (InfinitePlace.isReal_iff.mp hw)

include φ hc hc1 in
/-- The actual fixed-field quadratic extension is unramified at every finite prime. -/
theorem fixedField_finiteUnramified : FiniteUnramified (fixedField K c) K := by
  exact ImaginarySeven.finiteUnramified_of_real_place (fixedField K c) K
    (QuadraticSeven.fixedRoot φ c hc (sevenRootIn K) (sevenRootIn_sq K))
    (QuadraticSeven.fixedRoot_sq φ c hc (sevenRootIn K) (sevenRootIn_sq K))
    (imaginaryUnitIn K) (imaginaryUnitIn_sq K)
    (relativeDegree_eq_two φ c hc hc1) (nrRealPlaces_pos φ c hc)

include φ hc hc1 in
/-- Finite unramifiedness above the retained field fixes the actual root
 discriminant of each conjugation-fixed layer as well. -/
theorem fixedField_rootDiscriminant_eq
    (hM : FiniteUnramified RetainedField K) :
    rootDiscriminant (fixedField K c) = rootDiscriminant RetainedField := by
  rw [← rootDiscriminant_eq_of_finiteUnramified (fixedField K c) K
    (fixedField_finiteUnramified φ c hc hc1)]
  exact rootDiscriminant_eq_of_finiteUnramified RetainedField K hM

include φ hc hc1 in
/-- An actual conjugacy index gives the exact required signature bound. -/
theorem fixedField_signature_lower
    (hindex : 4096 ≤ (Subgroup.centralizer ({c} : Set Gal(K/ℚ))).index) :
    Witness.thetaMin ≤ RelativeUnits.signatureRatio (fixedField K c) := by
  have h := (complexPlaceRatio_bounds_4096 φ c hc hc1 (MonoidHom.id _) Function.surjective_id hindex).1
  exact h

end UnitDistance.GaloisConjugation
