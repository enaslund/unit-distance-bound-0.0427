module

public import UnitDistance.RetainedDyadicDifferentInertia
public import UnitDistance.ImaginarySevenUnramified
public import UnitDistance.ArithmeticCatalogIntegers

@[expose] public section
set_option backward.privateInPublic true


/-!
# An integral generator for the ramified retained quadratic direction

The retained root with index eleven has radicand `-2 + 3i`.  Over the
embedded eighth-cyclotomic field, the half-integral change of generator below
has derivative `(ζ²-ζ)x`.  These identities are the sharp arithmetic input for
the dyadic different estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField
namespace UnitDistance

namespace DyadicDifferentGenerator

variable {E : Type*} [Field E] [CharZero E]

def traceCoefficient (z : E) : E := -z ^ 3 - 3 * z ^ 2 + 2 * z - 2

def normCoefficient (z : E) : E := -3 * z ^ 3 + 5 * z ^ 2 - 5 * z

def transformedRoot (z x : E) : E :=
  (traceCoefficient z + (z ^ 2 - z) * x) / 2

theorem transformedRoot_equation (z x : E) (hz : z ^ 4 = -1)
    (hx : x ^ 2 = -2 + 3 * z ^ 2) :
    (transformedRoot z x) ^ 2 - traceCoefficient z * transformedRoot z x +
      normCoefficient z = 0 := by
  dsimp [transformedRoot, traceCoefficient, normCoefficient]
  field_simp
  ring_nf at hz hx ⊢
  linear_combination (z ^ 2 - z) ^ 2 * hx +
    2 * (z ^ 2 - 6 * z - 2) * hz

theorem transformedRoot_derivative (z x : E) :
    2 * transformedRoot z x - traceCoefficient z = (z ^ 2 - z) * x := by
  dsimp [transformedRoot]
  field_simp
  ring

end DyadicDifferentGenerator

namespace ArithmeticRetained

open ArithmeticChosenGenus ArithmeticCatalog Multiquadratic NumberField Polynomial

/-- The chosen square root of `-1` in the actual genus field. -/
abbrev dyadicI : GenusField := roots 0

/-- The chosen square root of `2` in the actual genus field. -/
abbrev dyadicSqrtTwo : GenusField := roots 1

/-- A primitive eighth root of unity in the actual genus field. -/
def dyadicZeta : GenusField := (1 + dyadicI) / dyadicSqrtTwo

theorem dyadicI_sq : dyadicI ^ 2 = -1 := by
  simpa [ArithmeticChosenGenus.radicands] using roots_sq 0

theorem dyadicSqrtTwo_sq : dyadicSqrtTwo ^ 2 = 2 := by
  simpa [ArithmeticChosenGenus.radicands] using roots_sq 1

theorem dyadicZeta_sq : dyadicZeta ^ 2 = dyadicI := by
  have hs : dyadicSqrtTwo ≠ 0 := roots_ne_zero 1
  dsimp [dyadicZeta]
  rw [div_pow, dyadicSqrtTwo_sq]
  field_simp
  linear_combination dyadicI_sq

theorem dyadicZeta_fourth : dyadicZeta ^ 4 = -1 := by
  rw [show dyadicZeta ^ 4 = (dyadicZeta ^ 2) ^ 2 by ring,
    dyadicZeta_sq, dyadicI_sq]

/-- The last retained squareclass is the explicit catalog radicand
`-2+3i`. -/
theorem retainedRadicand_eleven :
    retainedRadicand 11 = -2 + 3 * dyadicI := by
  have hword : CatalogSquareclassData.retainedWords 11 = 65536 := by decide
  have hfilter : Finset.univ.filter
      (fun i : Fin 17 => (65536 : ℕ).testBit i.val) = {16} := by
    ext i
    fin_cases i <;> decide
  have hroot : rootsA 16 = dyadicI := by
    rw [rootsA]
    have hmask : CatalogSquareclassData.masksA 16 = 1 := by decide
    change maskRoot (CatalogSquareclassData.masksA 16) = dyadicI
    rw [hmask]
    unfold maskRoot
    rw [Finset.prod_eq_single 0]
    · simp [dyadicI]
    · intro b hb hb0
      have hbit : (1 : ℕ).testBit b.val = false := by
        revert b
        decide
      simp [hbit]
    · simp
  rw [retainedRadicand, hword, wordRadicand, hfilter]
  simp only [NormExtensionCatalog.radicand, Finset.prod_singleton]
  change NormExtensionCatalog.alpha 16 (rootsA 16) = _
  rw [hroot]
  have hrow : NormExtensionCatalog.catalog 16 =
      ⟨-1, 13, -2, 3, 1⟩ := by decide
  rw [NormExtensionCatalog.alpha, hrow]
  norm_num

/-- The explicit transformed generator inside the actual retained field. -/
def dyadicIntegralCandidate : RetainedField :=
  DyadicDifferentGenerator.transformedRoot
    (algebraMap GenusField RetainedField dyadicZeta) (retainedRoot 11)

theorem retainedRoot_eleven_sq :
    (retainedRoot 11) ^ 2 =
      -2 + 3 * (algebraMap GenusField RetainedField dyadicZeta) ^ 2 := by
  rw [retainedRoot_sq, retainedRadicand_eleven, map_add, map_mul, map_neg,
    map_ofNat, map_ofNat, ← map_pow, dyadicZeta_sq]

theorem dyadicIntegralCandidate_equation :
    dyadicIntegralCandidate ^ 2 -
        algebraMap GenusField RetainedField
          (DyadicDifferentGenerator.traceCoefficient dyadicZeta) *
          dyadicIntegralCandidate +
        algebraMap GenusField RetainedField
          (DyadicDifferentGenerator.normCoefficient dyadicZeta) = 0 := by
  simpa [dyadicIntegralCandidate,
    DyadicDifferentGenerator.traceCoefficient,
    DyadicDifferentGenerator.normCoefficient, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat] using
    (DyadicDifferentGenerator.transformedRoot_equation
    (algebraMap GenusField RetainedField dyadicZeta) (retainedRoot 11)
    (by rw [← map_pow, dyadicZeta_fourth, map_neg, map_one])
    retainedRoot_eleven_sq)

theorem dyadicIntegralCandidate_derivative :
    2 * dyadicIntegralCandidate -
        algebraMap GenusField RetainedField
          (DyadicDifferentGenerator.traceCoefficient dyadicZeta) =
      ((algebraMap GenusField RetainedField dyadicZeta) ^ 2 -
        algebraMap GenusField RetainedField dyadicZeta) * retainedRoot 11 := by
  simpa [dyadicIntegralCandidate,
    DyadicDifferentGenerator.traceCoefficient, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat] using
    (DyadicDifferentGenerator.transformedRoot_derivative
      (E := RetainedField) (algebraMap GenusField RetainedField dyadicZeta)
        (retainedRoot 11))

/-- The global quadratic subfield carrying the ramified retained direction. -/
def RamifiedQuadraticField : IntermediateField GenusField RetainedField :=
  IntermediateField.adjoin GenusField ({retainedRoot 11} : Set RetainedField)

abbrev RamifiedField := RamifiedQuadraticField

def ramifiedRoot : RamifiedField :=
  ⟨retainedRoot 11, IntermediateField.subset_adjoin GenusField _ (Set.mem_singleton _)⟩

theorem ramifiedRoot_sq :
    ramifiedRoot ^ 2 = algebraMap GenusField RamifiedField (retainedRadicand 11) := by
  apply Subtype.ext
  exact retainedRoot_sq 11

theorem retainedRadicand_eleven_nonsquare :
    KummerInvariant.Nonsquare (retainedRadicand 11) := by
  intro s hs
  apply retained_products_not_isSquare ({11} : Finset (Fin 12)) (by simp)
  refine ⟨s, ?_⟩
  simpa [pow_two] using hs.symm

theorem retainedRadicand_eleven_not_isSquare :
    ¬ IsSquare (retainedRadicand 11) := by
  intro h
  obtain ⟨s, hs⟩ := h
  exact retainedRadicand_eleven_nonsquare s (by simpa [pow_two] using hs.symm)

theorem ramifiedRoot_isIntegral : IsIntegral GenusField ramifiedRoot := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (retainedRadicand 11),
    Polynomial.monic_X_pow_sub_C _ (by decide), ?_⟩
  simp [ramifiedRoot_sq]

theorem minpoly_ramifiedRoot :
    minpoly GenusField ramifiedRoot =
      Polynomial.X ^ 2 - Polynomial.C (retainedRadicand 11) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
      retainedRadicand_eleven_nonsquare
  · simp [ramifiedRoot_sq]
  · exact Polynomial.monic_X_pow_sub_C _ (by decide)

theorem retainedRoot_eleven_isIntegral :
    IsIntegral GenusField (retainedRoot 11) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (retainedRadicand 11),
    Polynomial.monic_X_pow_sub_C _ (by decide), ?_⟩
  simp [retainedRoot_sq]

theorem minpoly_retainedRoot_eleven :
    minpoly GenusField (retainedRoot 11) =
      Polynomial.X ^ 2 - Polynomial.C (retainedRadicand 11) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
      retainedRadicand_eleven_nonsquare
  · simp [retainedRoot_sq]
  · exact Polynomial.monic_X_pow_sub_C _ (by decide)

theorem ramifiedField_degree : Module.finrank GenusField RamifiedField = 2 := by
  change Module.finrank GenusField
    (IntermediateField.adjoin GenusField ({retainedRoot 11} : Set RetainedField)) = 2
  rw [IntermediateField.adjoin.finrank retainedRoot_eleven_isIntegral,
    minpoly_retainedRoot_eleven, Polynomial.natDegree_X_pow_sub_C]

theorem dyadicZeta_isIntegral : IsIntegral ℤ dyadicZeta := by
  apply IsIntegral.of_pow (n := 4) (by decide)
  rw [dyadicZeta_fourth]
  exact (isIntegral_one.neg)

theorem traceCoefficient_isIntegral :
    IsIntegral ℤ (DyadicDifferentGenerator.traceCoefficient dyadicZeta) := by
  have hz := dyadicZeta_isIntegral
  have h2 : IsIntegral ℤ (2 : GenusField) := isIntegral_natCast 2
  have h3 : IsIntegral ℤ (3 : GenusField) := isIntegral_natCast 3
  exact (((hz.pow 3).neg.sub (h3.mul (hz.pow 2))).add
    (h2.mul hz)).sub h2

theorem normCoefficient_isIntegral :
    IsIntegral ℤ (DyadicDifferentGenerator.normCoefficient dyadicZeta) := by
  have hz := dyadicZeta_isIntegral
  have hneg3 : IsIntegral ℤ (-3 : GenusField) :=
    (isIntegral_natCast 3 : IsIntegral ℤ (3 : GenusField)).neg
  have h5 : IsIntegral ℤ (5 : GenusField) := isIntegral_natCast 5
  simpa [DyadicDifferentGenerator.normCoefficient] using
    ((hneg3.mul (hz.pow 3)).add (h5.mul (hz.pow 2))).sub (h5.mul hz)

def traceInteger : RingOfIntegers GenusField :=
  ⟨DyadicDifferentGenerator.traceCoefficient dyadicZeta,
    traceCoefficient_isIntegral⟩

def normInteger : RingOfIntegers GenusField :=
  ⟨DyadicDifferentGenerator.normCoefficient dyadicZeta,
    normCoefficient_isIntegral⟩

def ramifiedZeta : RamifiedField := algebraMap GenusField RamifiedField dyadicZeta

def ramifiedIntegralCandidate : RamifiedField :=
  DyadicDifferentGenerator.transformedRoot ramifiedZeta ramifiedRoot

def ramifiedPolynomial : Polynomial (RingOfIntegers GenusField) :=
  Polynomial.X ^ 2 - Polynomial.C traceInteger * Polynomial.X +
    Polynomial.C normInteger

theorem ramifiedPolynomial_monic : ramifiedPolynomial.Monic := by
  unfold ramifiedPolynomial
  monicity <;> norm_num

theorem ramifiedIntegralCandidate_equation :
    ramifiedIntegralCandidate ^ 2 -
        algebraMap GenusField RamifiedField
          (DyadicDifferentGenerator.traceCoefficient dyadicZeta) *
          ramifiedIntegralCandidate +
        algebraMap GenusField RamifiedField
          (DyadicDifferentGenerator.normCoefficient dyadicZeta) = 0 := by
  simpa [ramifiedIntegralCandidate, ramifiedZeta,
    DyadicDifferentGenerator.traceCoefficient,
    DyadicDifferentGenerator.normCoefficient, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat] using
    (DyadicDifferentGenerator.transformedRoot_equation
      (algebraMap GenusField RamifiedField dyadicZeta) ramifiedRoot
      (by rw [← map_pow, dyadicZeta_fourth, map_neg, map_one])
      (by rw [ramifiedRoot_sq, retainedRadicand_eleven, map_add, map_mul, map_neg,
        map_ofNat, map_ofNat, ← map_pow, dyadicZeta_sq]))

theorem ramifiedIntegralCandidate_isIntegral :
    IsIntegral (RingOfIntegers GenusField) ramifiedIntegralCandidate := by
  refine ⟨ramifiedPolynomial, ramifiedPolynomial_monic, ?_⟩
  simpa [ramifiedPolynomial, traceInteger, normInteger,
    IsScalarTower.algebraMap_apply (RingOfIntegers GenusField) GenusField RamifiedField] using
      ramifiedIntegralCandidate_equation

def integralRamifiedCandidate : RingOfIntegers RamifiedField :=
  ⟨ramifiedIntegralCandidate,
    isIntegral_trans (A := RingOfIntegers GenusField) _
      ramifiedIntegralCandidate_isIntegral⟩

theorem ramifiedIntegralCandidate_derivative :
    2 * ramifiedIntegralCandidate -
        algebraMap GenusField RamifiedField
          (DyadicDifferentGenerator.traceCoefficient dyadicZeta) =
      (ramifiedZeta ^ 2 - ramifiedZeta) * ramifiedRoot := by
  simpa [ramifiedIntegralCandidate, ramifiedZeta,
    DyadicDifferentGenerator.traceCoefficient, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat] using
    (DyadicDifferentGenerator.transformedRoot_derivative
      (E := RamifiedField) ramifiedZeta ramifiedRoot)

theorem dyadicZeta_sq_sub_ne_zero : dyadicZeta ^ 2 - dyadicZeta ≠ 0 := by
  intro h
  have hz0 : dyadicZeta ≠ 0 := by
    intro hz
    have hfourth := dyadicZeta_fourth
    rw [hz] at hfourth
    norm_num at hfourth
  have hsq : dyadicZeta ^ 2 = dyadicZeta := sub_eq_zero.mp h
  have hz1 : dyadicZeta = 1 := by
    apply mul_left_cancel₀ hz0
    simpa [pow_two] using hsq
  have hfourth := dyadicZeta_fourth
  rw [hz1] at hfourth
  norm_num at hfourth

theorem ramifiedIntegralCandidate_generates :
    Algebra.adjoin GenusField ({ramifiedIntegralCandidate} : Set RamifiedField) = ⊤ := by
  let A := Algebra.adjoin GenusField ({ramifiedIntegralCandidate} : Set RamifiedField)
  have hc : ramifiedIntegralCandidate ∈ A :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  let d : GenusField := dyadicZeta ^ 2 - dyadicZeta
  have hd : d ≠ 0 := dyadicZeta_sq_sub_ne_zero
  have hdmap : algebraMap GenusField RamifiedField d =
      ramifiedZeta ^ 2 - ramifiedZeta := by
    simp [d, ramifiedZeta]
  have hprod : (ramifiedZeta ^ 2 - ramifiedZeta) * ramifiedRoot ∈ A := by
    rw [← ramifiedIntegralCandidate_derivative]
    exact A.sub_mem
      (A.mul_mem (by simpa using A.algebraMap_mem (2 : GenusField)) hc)
      (A.algebraMap_mem (DyadicDifferentGenerator.traceCoefficient dyadicZeta))
  have hx : ramifiedRoot ∈ A := by
    have he : ramifiedRoot = algebraMap GenusField RamifiedField d⁻¹ *
        (algebraMap GenusField RamifiedField d * ramifiedRoot) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hd, map_one, one_mul]
    rw [he]
    exact A.mul_mem (A.algebraMap_mem d⁻¹) (by simpa [hdmap] using hprod)
  let pb := IntermediateField.adjoin.powerBasis retainedRoot_eleven_isIntegral
  apply pb.adjoin_eq_top_of_gen_mem_adjoin
  exact hx

theorem integralRamifiedCandidate_aeval :
    Polynomial.aeval integralRamifiedCandidate ramifiedPolynomial = 0 := by
  apply RingOfIntegers.coe_injective
  simpa [ramifiedPolynomial, traceInteger, normInteger, integralRamifiedCandidate,
    map_ofNat, ← IsScalarTower.algebraMap_apply
      (RingOfIntegers GenusField) (RingOfIntegers RamifiedField) RamifiedField,
    IsScalarTower.algebraMap_apply
      (RingOfIntegers GenusField) GenusField RamifiedField] using
        ramifiedIntegralCandidate_equation

theorem ramifiedDerivative_mem_different :
    2 * integralRamifiedCandidate -
        algebraMap (RingOfIntegers GenusField) (RingOfIntegers RamifiedField)
          traceInteger ∈
      differentIdeal (RingOfIntegers GenusField) (RingOfIntegers RamifiedField) := by
  have h := ImaginarySeven.aeval_derivative_mem_different_of_aeval_zero
    GenusField RamifiedField integralRamifiedCandidate
      ramifiedIntegralCandidate_generates ramifiedPolynomial
      integralRamifiedCandidate_aeval
  norm_num [ramifiedPolynomial] at h
  simpa only [map_ofNat] using h

end ArithmeticRetained

end UnitDistance
