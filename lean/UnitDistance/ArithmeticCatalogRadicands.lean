module

public import UnitDistance.ArithmeticChosenGenusRoots
public import UnitDistance.NormExtensionCatalog
public import UnitDistance.CatalogSquareclassData

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual catalog radicands in the actual genus field

All square roots used in the norm catalog are explicit products of the seven
actual genus roots. The integer mask checks only select these actual elements;
their squares and actual automorphism actions are proved.
-/

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace UnitDistance.ArithmeticCatalog
open ArithmeticChosenGenus Multiquadratic NormExtensionCatalog

/-- Product of the independently defined rational genus radicands selected by a mask. -/
def maskValue (m : ℕ) : ℚ := ∏ j : Fin 7, if m.testBit j.val then radicands j else 1

/-- Actual genus-field square root selected by a mask. -/
def maskRoot (m : ℕ) : GenusField := ∏ j : Fin 7, if m.testBit j.val then roots j else 1

/-- The actual product root has the independently specified rational square. -/
theorem maskRoot_sq (m : ℕ) : (maskRoot m)^2 = (maskValue m : GenusField) := by
  unfold maskRoot maskValue
  rw [← Finset.prod_pow]
  push_cast
  apply Finset.prod_congr rfl
  intro j _
  split <;> simp [roots_sq]

/-- The actual binary character selected by the root mask. -/
abbrev maskCharacter := CatalogSquareclassData.character

/-- The explicit actual sign action on a product of actual square roots. -/
theorem signAutomorphism_maskRoot (m : ℕ) (v : Fin 7 → ZMod 2) :
    signAutomorphism v (maskRoot m) = binarySign (maskCharacter m v)*maskRoot m := by
  unfold maskRoot maskCharacter CatalogSquareclassData.character
  rw [map_prod,binarySign_sum,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  split <;> simp [signAutomorphism_roots]

/-- Rational square-root masks for the seventeen catalog A values. -/
abbrev masksA := CatalogSquareclassData.masksA

/-- Rational square-root masks for the seventeen catalog B values. -/
abbrev masksB := CatalogSquareclassData.masksB

/-- The independently specified masks match the actual integer catalog rows. -/
theorem maskValues_catalog (i : Fin 17) :
    maskValue (masksA i) = (catalog i).A ∧ maskValue (masksB i) = (catalog i).B := by
  have h : ∀ i : Fin 17,
      maskValue (masksA i) = (catalog i).A ∧ maskValue (masksB i) = (catalog i).B := by
    decide +kernel
  exact h i

/-- All actual A square roots used in the catalog. -/
def rootsA (i : Fin 17) : GenusField := maskRoot (masksA i)

/-- All actual B square roots used in the catalog. -/
def rootsB (i : Fin 17) : GenusField := maskRoot (masksB i)

theorem rootsA_sq (i : Fin 17) : (rootsA i)^2 = (catalog i).A := by
  rw [rootsA,maskRoot_sq,(maskValues_catalog i).1]
  norm_cast

theorem rootsB_sq (i : Fin 17) : (rootsB i)^2 = (catalog i).B := by
  rw [rootsB,maskRoot_sq,(maskValues_catalog i).2]
  norm_cast

/-- The actual seventeen algebraic radicands in the actual genus field. -/
def catalogAlpha (i : Fin 17) : GenusField := alpha i (rootsA i)

theorem catalogAlpha_ne_zero (i : Fin 17) : catalogAlpha i ≠ 0 :=
  alpha_ne_zero i (rootsA i) (rootsA_sq i)

/-- An actual radicand product specified by a raw catalog word. -/
def wordRadicand (m : ℕ) : GenusField :=
  radicand (Finset.univ.filter fun i : Fin 17 => m.testBit i.val) rootsA

theorem wordRadicand_ne_zero (m : ℕ) : wordRadicand m ≠ 0 :=
  radicand_ne_zero _ rootsA (fun i _ => rootsA_sq i)

/-- Every actual catalog word has invariant squareclass under the actual
Galois group of the explicitly constructed degree-128 genus field. -/
theorem wordRadicand_invariant (m : ℕ) (σ : Gal(GenusField/ℚ)) :
    ∃ u : GenusField, wordRadicand m*u^2 = σ (wordRadicand m) :=
  radicand_invariant σ _ rootsA rootsB rootsA_sq rootsB_sq

end UnitDistance.ArithmeticCatalog

namespace UnitDistance.ArithmeticCatalog
open ArithmeticChosenGenus Multiquadratic NormExtensionCatalog
abbrev F := ZMod 2

/-- The Bool sign convention in the norm catalog agrees with the actual
binary character sign. -/
theorem catalogSign_eq_binarySign (x : F) :
    (sign (decide (x ≠ 0)) : GenusField) = binarySign x := by
  by_cases h : x = 0 <;> simp [sign,binarySign,binarySignInteger,h]

theorem catalogSign_mul_eq_binarySign (x y : F) :
    (sign (decide (x ≠ 0) && decide (y ≠ 0)) : GenusField) = binarySign (x*y) := by
  have h : ∀ x y : F, (decide (x ≠ 0) && decide (y ≠ 0)) = decide (x*y ≠ 0) := by
    decide +kernel
  rw [h,catalogSign_eq_binarySign]

/-- The explicit actual sign-lift multiplier for a raw catalog word. -/
def wordMultiplier (m : ℕ) (v : Fin 7 → F) : GenusField :=
  productMultiplier (Finset.univ.filter fun i : Fin 17 => m.testBit i.val)
    rootsA rootsB (fun i => decide (maskCharacter (masksA i) v ≠ 0))

/-- The actual sign automorphism acts on every catalog A root as computed. -/
theorem signAutomorphism_rootsA (v : Fin 7 → F) (i : Fin 17) :
    signAutomorphism v (rootsA i) =
      sign (decide (maskCharacter (masksA i) v ≠ 0))*rootsA i := by
  rw [catalogSign_eq_binarySign]
  exact signAutomorphism_maskRoot (masksA i) v

/-- The actual sign automorphism acts on every catalog B root as computed. -/
theorem signAutomorphism_rootsB (v : Fin 7 → F) (i : Fin 17) :
    signAutomorphism v (rootsB i) =
      sign (decide (maskCharacter (masksB i) v ≠ 0))*rootsB i := by
  rw [catalogSign_eq_binarySign]
  exact signAutomorphism_maskRoot (masksB i) v

/-- The independently computed sign multiplier satisfies the actual field twist identity. -/
theorem wordMultiplier_twist (m : ℕ) (v : Fin 7 → F) :
    wordRadicand m*(wordMultiplier m v)^2 = signAutomorphism v (wordRadicand m) := by
  apply productMultiplier_twist
  · exact fun i _ => rootsA_sq i
  · exact fun i _ => rootsB_sq i
  · exact fun i _ => signAutomorphism_rootsA v i

/-- The independently computed binary word form is the actual twisted norm
of the actual field lift multiplier. -/
theorem wordMultiplier_twisted_norm (m : ℕ) (v : Fin 7 → F) :
    wordMultiplier m v * signAutomorphism v (wordMultiplier m v) =
      binarySign (CatalogSquareclassData.wordForm m v) := by
  have hn := productMultiplier_twisted_norm (signAutomorphism v)
    (Finset.univ.filter fun i : Fin 17 => m.testBit i.val) rootsA rootsB
    (fun i _ => rootsA_sq i) (fun i _ => rootsB_sq i)
    (fun i => decide (maskCharacter (masksA i) v ≠ 0))
    (fun i => decide (maskCharacter (masksB i) v ≠ 0))
    (fun i _ => signAutomorphism_rootsA v i) (fun i _ => signAutomorphism_rootsB v i)
  change wordMultiplier m v * signAutomorphism v (wordMultiplier m v) = _ at hn
  rw [hn]
  simp_rw [catalogSign_mul_eq_binarySign]
  rw [← binarySign_sum]
  congr 1
  simp only [CatalogSquareclassData.wordForm,CatalogSquareclassData.catalogForm,
    Finset.sum_filter,maskCharacter,masksA,masksB]

/-- A nonzero independently computed word form proves actual nonsquareness
of that explicitly constructed genus-field radicand. -/
theorem wordRadicand_nonsquare (m : ℕ) (v : Fin 7 → F)
    (hform : CatalogSquareclassData.wordForm m v ≠ 0) :
    KummerInvariant.Nonsquare (wordRadicand m) := by
  apply KummerInvariant.nonsquare_of_twisted_norm (signAutomorphism v)
    (signAutomorphism_involutive v) (wordRadicand m) (wordMultiplier m v)
    (wordRadicand_ne_zero m) (wordMultiplier_twist m v)
  rw [wordMultiplier_twisted_norm]
  intro h
  apply hform
  apply binarySign_injective (E := GenusField)
  simpa using h

end UnitDistance.ArithmeticCatalog
