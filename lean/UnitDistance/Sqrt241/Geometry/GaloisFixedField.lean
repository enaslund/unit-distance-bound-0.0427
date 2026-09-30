module

public import UnitDistance.GaloisFixedArithmetic
public import UnitDistance.Sqrt241.Geometry.ImaginaryRootUnramified
public import UnitDistance.Sqrt241.Geometry.QuadraticRootConjugation
public import UnitDistance.Sqrt241.Witness

@[expose] public section
set_option backward.privateInPublic true


/-!
# Conjugation-fixed fields above a base field containing `√3` and `√-1`

Copy of `UnitDistance.GaloisFixedArithmetic`. The ℚ retained field, with its
displayed `√7` and `i`, is replaced by an arbitrary number field `M` carrying
elements `r3² = 3` and `ii² = -1`; the radicand `3` is admissible
(`QuadraticRoot.admissible_three`). A centralizer index of at least `2^16`
gives `Sqrt241.Witness.thetaMin = 65535/131072` through the parametric
`GaloisConjugation.complexPlaceRatio_bounds_of_retained_index`.
-/

noncomputable section
set_option autoImplicit false
open NumberField NumberField.ComplexEmbedding
namespace UnitDistance.Sqrt241.GaloisConjugation
open UnitDistance.NumberFieldAnalysis UnitDistance.GaloisConjugation

variable {K : Type} [Field K] [NumberField K] [IsGalois ℚ K]
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

/-- A displayed square root of `-1` excludes every real place. -/
theorem totallyComplex_of_sqrt_neg_one (x : K) (hx : x^2 = -1) : IsTotallyComplex K := by
  refine ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mp ?_⟩
  intro hw
  exact not_isReal_of_sqrt_neg_one w.embedding x hx (InfinitePlace.isReal_iff.mp hw)

variable {M : Type} [Field M] [NumberField M] [Algebra M K]
  (r3 : M) (hr3 : r3^2 = 3) (ii : M) (hii : ii^2 = -1)

include hr3 in
theorem algebraMap_root_sq : (algebraMap M K r3)^2 = ((3 : ℕ) : K) := by
  rw [← map_pow, hr3, map_ofNat]
  norm_num

include hii in
theorem algebraMap_imaginary_sq : (algebraMap M K ii)^2 = -1 := by
  rw [← map_pow, hii, map_neg, map_one]

include φ hc hc1 hr3 hii in
/-- The actual fixed-field quadratic extension is unramified at every finite prime. -/
theorem fixedField_finiteUnramified : FiniteUnramified (fixedField K c) K := by
  exact ImaginaryRoot.finiteUnramified_of_real_place (fixedField K c) K
    (QuadraticRoot.fixedRoot φ c hc (algebraMap M K r3) (algebraMap_root_sq r3 hr3))
    (QuadraticRoot.fixedRoot_sq φ c hc (algebraMap M K r3) (algebraMap_root_sq r3 hr3))
    (algebraMap M K ii) (algebraMap_imaginary_sq ii hii)
    (relativeDegree_eq_two φ c hc hc1) (nrRealPlaces_pos φ c hc)

include φ hc hc1 hr3 hii in
/-- Finite unramifiedness above the base field fixes the actual root
discriminant of each conjugation-fixed layer as well. -/
theorem fixedField_rootDiscriminant_eq (hM : FiniteUnramified M K) :
    rootDiscriminant (fixedField K c) = rootDiscriminant M := by
  rw [← rootDiscriminant_eq_of_finiteUnramified (fixedField K c) K
    (fixedField_finiteUnramified φ c hc hc1 r3 hr3 ii hii)]
  exact rootDiscriminant_eq_of_finiteUnramified M K hM

include φ hc hc1 in
/-- A centralizer index of at least `2^16` gives the signature bound
`Sqrt241.Witness.thetaMin`. -/
theorem fixedField_signature_lower
    (hindex : 65536 ≤ (Subgroup.centralizer ({c} : Set Gal(K/ℚ))).index) :
    Witness.thetaMin ≤ RelativeUnits.signatureRatio (fixedField K c) := by
  have h := (complexPlaceRatio_bounds_of_retained_index φ c hc hc1 (MonoidHom.id _)
    Function.surjective_id 65536 (by norm_num) hindex).1
  have ht : Witness.thetaMin = (1-1/((65536 : ℕ) : ℝ))/2 := by
    norm_num [Witness.thetaMin]
  rw [ht]
  exact h

end UnitDistance.Sqrt241.GaloisConjugation
