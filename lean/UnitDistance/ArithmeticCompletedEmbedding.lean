module

public import UnitDistance.ArithmeticRetainedField
public import UnitDistance.ArithmeticCompletedField
public import UnitDistance.ArithmeticCatalogSquareRelation
public import UnitDistance.CatalogCompletedContainmentData
public import UnitDistance.GeneratedQuadraticEmbedding

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual embedding of the completed field in the full retained field

The exact raw-word identities, including the explicit square relation word26,
show that all seven completed radicands become squares in the actual
12-radical retained field. Generation then supplies an actual field embedding.
-/
noncomputable section
namespace UnitDistance.ArithmeticCompleted
open ArithmeticChosenGenus ArithmeticCatalog ArithmeticRetained Multiquadratic
  CatalogWordSquareclasses CatalogCompletedContainmentData

private theorem mapped_wordValue (m : ℕ) :
    wordValue (fun i => algebraMap GenusField RetainedField (catalogAlpha i)) m =
      algebraMap GenusField RetainedField (wordRadicand m) := by
  rw [wordRadicand_eq_wordValue]
  simp only [wordValue,map_prod]
  apply Finset.prod_congr rfl
  intro i _
  split <;> simp_all

/-- Every completed radicand is an actual square in the retained field. -/
theorem completedRadicand_isSquare_retained (j : Fin 7) :
    IsSquare (algebraMap GenusField RetainedField (completedRadicand j)) := by
  let a : Fin 17 → RetainedField := fun i =>
    algebraMap GenusField RetainedField (catalogAlpha i)
  have hn : ∀ i, a i ≠ 0 := by
    intro i
    simpa [a] using catalogAlpha_ne_zero i
  have hs : ∀ m ∈ combinationWords j, IsSquare (wordValue a m) := by
    intro m hm
    rw [show wordValue a m = algebraMap GenusField RetainedField (wordRadicand m) from
      mapped_wordValue m]
    rcases mem_combinationWords j m hm with ⟨k,rfl⟩ | rfl
    · obtain ⟨x,hx⟩ := retainedField_contains_radical k
      exact ⟨x,by simpa [retainedRadicand,pow_two] using hx.symm⟩
    · obtain ⟨x,hx⟩ := wordRadicand_26_isSquare
      exact ⟨algebraMap GenusField RetainedField x,by
        simpa only [map_mul] using congrArg (algebraMap GenusField RetainedField) hx⟩
  have h := isSquare_word_fold a hn (combinationWords j) hs
  rw [combination_certificate] at h
  change IsSquare (wordValue (fun i => algebraMap GenusField RetainedField (catalogAlpha i))
    (CatalogSquareclassData.completedWords j)) at h
  rwa [mapped_wordValue] at h

/-- The retained field contains an actual root of each completed radicand. -/
theorem retained_contains_completed_radical (j : Fin 7) :
    ∃ x : RetainedField, x^2=algebraMap GenusField RetainedField (completedRadicand j) := by
  obtain ⟨x,hx⟩ := completedRadicand_isSquare_retained j
  exact ⟨x,by simpa [pow_two] using hx.symm⟩

/-- An actual genus-field embedding of N into M. -/
def completedEmbedding : CompletedField →ₐ[GenusField] RetainedField :=
  Classical.choice (completedTower.nonempty_embedding RetainedField
    (fun i _ => retained_contains_completed_radical i))

/-- The same actual field embedding over the rational numbers. -/
def completedEmbeddingRat : CompletedField →ₐ[ℚ] RetainedField :=
  completedEmbedding.toRingHom.toRatAlgHom

end UnitDistance.ArithmeticCompleted
