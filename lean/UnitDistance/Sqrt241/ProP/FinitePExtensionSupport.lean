/-
Retyped from `UnitDistance/FinitePExtensionSupport.lean` (adapted from Naganori
Yamaguchi's SawinTotallyRealTowers, commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4,
Apache-2.0): ℚ is replaced by an arbitrary number field `F`.
-/
module

public import UnitDistance.Sqrt241.ProP.FinitePExtension
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Finite support in the pro-p tower over a number field

Compact intermediate fields contained in the supremum of admissible finite
layers lie in one layer, since the family is nonempty and directed.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.ProP

open ClassFieldTower.Sawin

variable (F : Type) [Field F] [NumberField F]

/-- A finite-dimensional intermediate field is a compact element. -/
theorem finiteDimensional_intermediateField_isCompactElement
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (L : IntermediateField K E) [FiniteDimensional K L] : IsCompactElement L := by
  have hEss : Algebra.EssFiniteType K L := inferInstance
  obtain ⟨s, hs⟩ := IntermediateField.essFiniteType_iff.mp hEss
  rw [← hs]
  exact IntermediateField.adjoin_finset_isCompactElement s

theorem compact_le_iSup_pExtension_exists_extension
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (L : IntermediateField F (AlgebraicClosure F))
    (hCompact : IsCompactElement L)
    (hL : L ≤ ⨆ E : FinitePExtension F p T, E.val.toIntermediateField) :
    ∃ C : FinitePExtension F p T, L ≤ C.val.toIntermediateField := by
  let f : FinitePExtension F p T → IntermediateField F (AlgebraicClosure F) :=
    fun E ↦ E.val.toIntermediateField
  have hNonempty : (Set.range f).Nonempty :=
    ⟨f (FinitePExtension.bot F p T), ⟨FinitePExtension.bot F p T, rfl⟩⟩
  have hDirected : DirectedOn (· ≤ ·) (Set.range f) :=
    (FinitePExtension.directed F p T).directedOn_range
  have hLe : L ≤ sSup (Set.range f) := by
    simpa only [sSup_range] using hL
  obtain ⟨M, hM, hLM⟩ :=
    (isCompactElement_iff_le_of_directed_sSup_le L).mp hCompact
        (Set.range f) hNonempty hDirected hLe
  rcases hM with ⟨C, rfl⟩
  exact ⟨C, hLM⟩

/-- A finite-dimensional intermediate field in the supremum of admissible
finite layers is contained in one admissible finite layer. -/
theorem finiteDimensional_le_iSup_pExtension_exists_extension
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L]
    (hL : L ≤ ⨆ E : FinitePExtension F p T, E.val.toIntermediateField) :
    ∃ C : FinitePExtension F p T, L ≤ C.val.toIntermediateField := by
  exact compact_le_iSup_pExtension_exists_extension F p T L
    (finiteDimensional_intermediateField_isCompactElement L) hL

/-- Finitely many elements of the supremum all belong to a single admissible
finite layer. -/
theorem finset_subset_iSup_pExtension_exists_extension
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (s : Finset (AlgebraicClosure F))
    (hs : ∀ x ∈ s, x ∈ ⨆ E : FinitePExtension F p T, E.val.toIntermediateField) :
    ∃ C : FinitePExtension F p T, ∀ x ∈ s, x ∈ C.val.toIntermediateField := by
  have hAdjoin : IntermediateField.adjoin F (s : Set (AlgebraicClosure F)) ≤
      ⨆ E : FinitePExtension F p T, E.val.toIntermediateField :=
    IntermediateField.adjoin_le_iff.mpr (by
      intro x hx
      exact hs x hx)
  obtain ⟨C, hC⟩ := compact_le_iSup_pExtension_exists_extension F p T
    (IntermediateField.adjoin F (s : Set (AlgebraicClosure F)))
    (IntermediateField.adjoin_finset_isCompactElement (F := F) s) hAdjoin
  refine ⟨C, ?_⟩
  intro x hx
  exact hC (IntermediateField.subset_adjoin F (s : Set (AlgebraicClosure F)) hx)

end UnitDistance.Sqrt241.ProP
