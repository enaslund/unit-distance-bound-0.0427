module

public import UnitDistance.GeneratedQuadraticRamification
public import UnitDistance.ArithmeticCatalogIntegers
public import UnitDistance.ArithmeticRetainedField
public import UnitDistance.ArithmeticCompletedField

@[expose] public section
set_option backward.privateInPublic true


/-! Actual ramification support of the chosen genus field and the manuscript's
finite retained fields M and N. All radicands and complementary integral
factors are the concrete catalog quantities. -/
noncomputable section
open NumberField
namespace UnitDistance
open Multiquadratic QuadraticRamification

namespace ArithmeticChosenGenus

private def integerRadicands : Fin 7 → ℤ := ![-1,2,3,5,7,11,13]

private theorem integerRadicands_coe (i : Fin 7) :
    ((integerRadicands i : 𝓞 ℚ) : ℚ) = radicands i := by
  fin_cases i <;> norm_num [integerRadicands, radicands, RingOfIntegers.coe_eq_algebraMap, map_ofNat]

private theorem integerRadicands_divides (i : Fin 7) : integerRadicands i ∣ (30030:ℤ) := by
  fin_cases i <;> norm_num [integerRadicands]

/-- The actual chosen seven-radical genus field has finite ramification only in Σ. -/
theorem genusField_unramifiedAway : UnramifiedAway GenusField 30030 := by
  letI : IsGalois ℚ ℚ := IsGalois.self ℚ
  letI : @IsGalois ℚ _ ℚ _ DivisionRing.toRatAlgebra := by
    have he : (DivisionRing.toRatAlgebra : Algebra ℚ ℚ) = Algebra.id ℚ := Subsingleton.elim _ _
    rw [he]
    exact IsGalois.self ℚ
  apply genusTower.unramifiedAway radicands_ne_zero rational_products_nonsquare
    radicands_invariant (unramifiedAway_rat 30030)
  intro i
  exact ⟨(integerRadicands i : 𝓞 ℚ), 1, integerRadicands i, 1,
    integerRadicands_coe i, by simp, by simpa using integerRadicands_divides i⟩

end ArithmeticChosenGenus

namespace ArithmeticCatalog

/-- Every actual catalog word supplies the integral data used by the generated
ramification theorem. -/
theorem word_integral_ramification_data (w : ℕ) :
    ∃ a b : 𝓞 ArithmeticChosenGenus.GenusField, ∃ n : ℤ, ∃ m : ℕ,
      (a:ArithmeticChosenGenus.GenusField) = wordRadicand w ∧
      a*b = n ∧ n ∣ (30030:ℤ)^m := by
  obtain ⟨b,n,m,hprod,hdiv⟩ := wordInteger_hasSigmaComplement w
  exact ⟨wordInteger w,b,n,m,wordInteger_coe w,hprod,hdiv⟩

end ArithmeticCatalog

namespace ArithmeticRetained

/-- The actual degree-2^19 retained field M is unramified outside Σ. -/
theorem retainedField_unramifiedAway : UnramifiedAway RetainedField 30030 := by
  apply fullRetainedTower.unramifiedAway retainedRadicand_ne_zero retained_products_not_isSquare
    retainedRadicand_invariant ArithmeticChosenGenus.genusField_unramifiedAway
  intro i
  exact ArithmeticCatalog.word_integral_ramification_data (CatalogSquareclassData.retainedWords i)

end ArithmeticRetained

namespace ArithmeticCompleted

/-- The actual degree-2^14 completed field N is unramified outside Σ. -/
theorem completedField_unramifiedAway : UnramifiedAway CompletedField 30030 := by
  apply completedTower.unramifiedAway completedRadicand_ne_zero completed_products_not_isSquare
    completedRadicand_invariant ArithmeticChosenGenus.genusField_unramifiedAway
  intro i
  exact ArithmeticCatalog.word_integral_ramification_data (CatalogSquareclassData.completedWords i)

end ArithmeticCompleted
end UnitDistance
