module

public import UnitDistance.ArithmeticGenusSquareClasses
public import UnitDistance.FiniteFieldImage
public import UnitDistance.SigmaPrimeSupport
public import UnitDistance.UnramifiedAwayDiscriminant
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.QuadraticSquarefreeGenerator
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.QuadraticFieldDiscriminant

@[expose] public section
set_option backward.privateInPublic true


/-!
# All quadratic subfields supported at the six finite primes

Actual unramifiedness, signed quadratic discriminants, and the seven actual
roots identify every allowed quadratic field inside the genus-field image.
Infinite places are unrestricted. The lifting identity in the final proof
also appears in Yamaguchi's QuadraticClosureClassification (Apache-2.0).
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP
open NumberField QuadraticRamification ArithmeticChosenGenus ClassFieldTower.Sawin

/-- Actual finite ramification support forces a signed squarefree quadratic
generator whose prime divisors are among the six specified primes. -/
theorem exists_supported_quadratic_generator_of_discriminant_support
    (L : Type*) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (hds : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr L → p ∈ finitePrimeSupport) :
    ∃ d : ℤ, ∃ β : L,
      Squarefree d.natAbs ∧ β ^ 2 = algebraMap ℚ L (d : ℚ) ∧
      IntermediateField.adjoin ℚ ({β} : Set L) = ⊤ ∧
      ¬ IsSquare (d : ℚ) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → p ∈ finitePrimeSupport) := by
  obtain ⟨d, β, hsf, _hd, hsq, hgen, hnsq⟩ :=
    exists_squarefree_int_generator_of_isQuadraticExtension L
  refine ⟨d, β, hsf, hsq, hgen, hnsq, ?_⟩
  intro p hp hpd
  have hdisc : (p : ℤ) ∣ discr L := by
    by_cases hm : d % 4 = 1
    · rw [numberField_discr_of_mod_four_eq_one L d hsf β hsq hgen hm]
      exact hpd
    · rw [numberField_discr_of_mod_four_ne_one L d hsf β hsq hgen hm]
      exact dvd_mul_of_dvd_right hpd 4
  exact hds p hp hdisc

/-- Every actual quadratic subfield unramified outside the six finite
primes lies in the literal image of the actual degree-128 genus field. -/
theorem quadratic_le_genusImage_of_discriminant_support
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField E]
    (hdegree : Module.finrank ℚ E = 2)
    (hds : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ finitePrimeSupport) :
    E.toIntermediateField ≤ (finiteGaloisImage GenusField).toIntermediateField := by
  letI : Algebra.IsQuadraticExtension ℚ E := ⟨hdegree⟩
  let M := (finiteGaloisImage GenusField).toIntermediateField
  letI : Algebra GenusField M := (finiteGaloisImageEquiv GenusField).toAlgHom.toAlgebra
  obtain ⟨d, β, hsf, hsq, hgen, _hnsq, hs⟩ :=
    exists_supported_quadratic_generator_of_discriminant_support E hds
  have hsq' : (β : AlgebraicClosure ℚ) ^ 2 = (d : AlgebraicClosure ℚ) := by
    have hsq0 : β ^ 2 = (d : E) := by simpa only [map_intCast] using hsq
    have h := congrArg (fun z : E ↦ (z : AlgebraicClosure ℚ)) hsq0
    change (β : AlgebraicClosure ℚ) ^ 2 = (d : AlgebraicClosure ℚ) at h
    exact h
  have hmem : (β : AlgebraicClosure ℚ) ∈ M :=
    root_mem_of_supported (AlgebraicClosure ℚ) M d hsf hs β hsq'
  have heq : E.toIntermediateField =
      IntermediateField.adjoin ℚ ({(β : AlgebraicClosure ℚ)} : Set (AlgebraicClosure ℚ)) := by
    calc
      E.toIntermediateField = IntermediateField.lift
          (⊤ : IntermediateField ℚ E.toIntermediateField) :=
        (IntermediateField.lift_top ℚ E.toIntermediateField).symm
      _ = IntermediateField.lift (IntermediateField.adjoin ℚ ({β} : Set E)) :=
        congrArg (fun L : IntermediateField ℚ E ↦ IntermediateField.lift L) hgen.symm
      _ = IntermediateField.adjoin ℚ {(β : AlgebraicClosure ℚ)} :=
        IntermediateField.lift_adjoin_simple ℚ E.toIntermediateField β
  rw [heq]
  exact IntermediateField.adjoin_simple_le_iff.mpr hmem

/-- Actual local unramifiedness supplies the independently defined
discriminant support used in the classification. -/
theorem discriminant_support_of_unramifiedAway
    (L : Type*) [Field L] [NumberField L] (hu : UnramifiedAway L 30030) :
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr L → p ∈ finitePrimeSupport := by
  intro p hp hd
  apply (prime_dvd_sigma_product_iff hp).mp
  have h : (p : ℤ) ∣ 30030 :=
    hu.prime_dvd_of_dvd_discr (Nat.prime_iff_prime_int.mp hp) hd
  exact_mod_cast h

/-- Actual finite ramification support forces a supported signed generator. -/
theorem exists_supported_quadratic_generator
    (L : Type*) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (hu : UnramifiedAway L 30030) :
    ∃ d : ℤ, ∃ β : L,
      Squarefree d.natAbs ∧ β ^ 2 = algebraMap ℚ L (d : ℚ) ∧
      IntermediateField.adjoin ℚ ({β} : Set L) = ⊤ ∧
      ¬ IsSquare (d : ℚ) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → p ∈ finitePrimeSupport) :=
  exists_supported_quadratic_generator_of_discriminant_support L
    (discriminant_support_of_unramifiedAway L hu)

/-- Every actual quadratic subfield unramified outside the six finite
primes lies in the actual genus-field image. -/
theorem quadratic_le_genusImage
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField E]
    (hdegree : Module.finrank ℚ E = 2) (hu : UnramifiedAway E 30030) :
    E.toIntermediateField ≤ (finiteGaloisImage GenusField).toIntermediateField :=
  quadratic_le_genusImage_of_discriminant_support E hdegree
    (discriminant_support_of_unramifiedAway E hu)

end UnitDistance.ArithmeticProP
