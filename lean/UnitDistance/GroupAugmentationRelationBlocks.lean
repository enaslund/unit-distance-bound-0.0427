module

public import UnitDistance.GroupAugmentationGlobalCommonRow

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual relation coverage proves global block spanning and common inclusion

The global blocks are restrictions of genuine left-algebra submodules.
Covering actual completed defining relations by substituted local relations
therefore proves the global block-spanning equality from Fox exactness.
Covering only the original relations by the other local blocks proves the
common-row inclusion needed for the optimized subtraction.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
universe u
variable (P : Type u) [Group P] [Finite P]
local notation "F" => ZMod 2
variable {ι κ : Type u} [Fintype ι] [Fintype κ]
variable (generators : ι → P) (words : κ → FreeGroup ι)

/-- The actual global local-kernel image as a left-algebra submodule. -/
def globalFoxBlockAlgebra : Submodule (A F P) (ι → A F P) :=
  ((foxMapAlgebra F P (fun j => FreeGroup.lift generators (words j))).ker).map
    (foxSubstitutionAlgebra F P generators words)

/-- Scalar restriction recovers exactly the previously defined filtered
vector subspace; no extra vectors are inserted by the algebra formulation. -/
theorem globalFoxBlockAlgebra_restrict :
    (globalFoxBlockAlgebra P generators words).restrictScalars F =
      globalFoxBlock P generators words := by
  ext a
  rfl

/-- A substituted actual completed local relation gives a row in its actual
full global local block. -/
theorem completedFoxDerivative_mem_globalBlock (s : CompletedWords κ)
    (hs : completedWordEvaluation P (fun j => FreeGroup.lift generators (words j)) s = 1) :
    completedFoxDerivative P generators (completedSubstitution words s) ∈
      globalFoxBlockAlgebra P generators words := by
  rw [completedFoxDerivative_substitution]
  refine ⟨completedFoxDerivative P (fun j => FreeGroup.lift generators (words j)) s,?_,rfl⟩
  change foxMap F P (fun j => FreeGroup.lift generators (words j))
    (completedFoxDerivative P (fun j => FreeGroup.lift generators (words j)) s) = 0
  rw [completedFoxDerivative_fundamental,hs]
  simp

variable {J : Type*} (κs : J → Type u) [∀ j, Fintype (κs j)]
variable (localWords : ∀ j, κs j → FreeGroup ι)

/-- Relation coverage is literal equality with substituted completed words,
plus actual vanishing in the corresponding local generator evaluation. -/
def CompletedRelationCoverage (relations : Set (CompletedWords ι)) : Prop :=
  ∀ r ∈ relations, ∃ (j : J) (s : CompletedWords (κs j)),
    completedWordEvaluation P (fun i => FreeGroup.lift generators (localWords j i)) s = 1 ∧
      completedSubstitution (localWords j) s = r

/-- Covering the displayed relations places their entire left-algebra row
module inside the sum of the selected actual global blocks. -/
theorem completedRelationModule_le_blocks (relations : Set (CompletedWords ι))
    (hcover : CompletedRelationCoverage P generators κs localWords relations) :
    completedFoxRelationModule P generators relations ≤
      ⨆ j, globalFoxBlockAlgebra P generators (localWords j) := by
  apply Submodule.span_le.mpr
  rintro a ⟨r,hr,rfl⟩
  obtain ⟨j,s,hs,rfl⟩ := hcover r hr
  exact (le_iSup (fun j => globalFoxBlockAlgebra P generators (localWords j)) j)
    (completedFoxDerivative_mem_globalBlock P generators (localWords j) s hs)

/-- The same actual row-span inclusion in the ambient coefficient vector
space, ready for the filtered subspace intersection theorem. -/
theorem completedRelationModule_restrict_le_blocks (relations : Set (CompletedWords ι))
    (hcover : CompletedRelationCoverage P generators κs localWords relations) :
    (completedFoxRelationModule P generators relations).restrictScalars F ≤
      ⨆ j, globalFoxBlock P generators (localWords j) := by
  have he := completedRelationModule_le_blocks P generators κs localWords relations hcover
  have he' := Submodule.restrictScalars_mono F he
  simpa only [Submodule.restrictScalars_iSup,globalFoxBlockAlgebra_restrict] using he'

/-- Actual completed Fox exactness and actual relation coverage prove the
whole global-kernel spanning equality by full local blocks. -/
theorem foxKernel_eq_blocks_of_completedPresentation (hP : IsPGroup 2 P)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (relations : Set (CompletedWords ι))
    (hpresentation : CompletedProTwoPresentation P generators relations)
    (hcover : CompletedRelationCoverage P generators κs localWords relations) :
    (foxMap F P generators).ker = ⨆ j, globalFoxBlock P generators (localWords j) := by
  apply le_antisymm
  · rw [foxKernel_eq_completedRelationModule P generators relations hP hgen hpresentation]
    exact completedRelationModule_restrict_le_blocks P generators κs localWords relations hcover
  · apply iSup_le
    intro j
    exact globalFoxBlock_le_kernel P generators (localWords j)

/-- A weaker coverage input compares actual evaluated rows, so it also
applies when the arithmetic global generator lifts are completed words and
literal words are chosen only to match their finite affine evaluations. -/
def CompletedFoxRowCoverage (relations : Set (CompletedWords ι)) : Prop :=
  ∀ r ∈ relations, ∃ (j : J) (s : CompletedWords (κs j)),
    completedWordEvaluation P (fun i => FreeGroup.lift generators (localWords j i)) s = 1 ∧
      completedFoxDerivative P generators r =
        completedFoxDerivative P generators (completedSubstitution (localWords j) s)

/-- Literal completed-word coverage implies the weaker evaluated-row form. -/
theorem CompletedRelationCoverage.rowCoverage (relations : Set (CompletedWords ι))
    (hcover : CompletedRelationCoverage P generators κs localWords relations) :
    CompletedFoxRowCoverage P generators κs localWords relations := by
  intro r hr
  obtain ⟨j,s,hs,he⟩ := hcover r hr
  exact ⟨j,s,hs,congrArg (completedFoxDerivative P generators) he.symm⟩

/-- Actual row coverage suffices to place the whole relation module inside
the selected algebra blocks. -/
theorem completedRelationModule_le_blocks_of_rowCoverage
    (relations : Set (CompletedWords ι))
    (hcover : CompletedFoxRowCoverage P generators κs localWords relations) :
    completedFoxRelationModule P generators relations ≤
      ⨆ j, globalFoxBlockAlgebra P generators (localWords j) := by
  apply Submodule.span_le.mpr
  rintro a ⟨r,hr,rfl⟩
  obtain ⟨j,s,hs,he⟩ := hcover r hr
  rw [he]
  exact (le_iSup (fun j => globalFoxBlockAlgebra P generators (localWords j)) j)
    (completedFoxDerivative_mem_globalBlock P generators (localWords j) s hs)

/-- Evaluated-row coverage gives the actual induced vector-subspace inclusion. -/
theorem completedRelationModule_restrict_le_blocks_of_rowCoverage
    (relations : Set (CompletedWords ι))
    (hcover : CompletedFoxRowCoverage P generators κs localWords relations) :
    (completedFoxRelationModule P generators relations).restrictScalars F ≤
      ⨆ j, globalFoxBlock P generators (localWords j) := by
  have he := completedRelationModule_le_blocks_of_rowCoverage P generators κs localWords relations hcover
  have he' := Submodule.restrictScalars_mono F he
  simpa only [Submodule.restrictScalars_iSup,globalFoxBlockAlgebra_restrict] using he'

/-- Complete presentation and actual row coverage prove full kernel spanning,
without identifying arbitrary completed generator lifts with finite words. -/
theorem foxKernel_eq_blocks_of_rowCoverage (hP : IsPGroup 2 P)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (relations : Set (CompletedWords ι))
    (hpresentation : CompletedProTwoPresentation P generators relations)
    (hcover : CompletedFoxRowCoverage P generators κs localWords relations) :
    (foxMap F P generators).ker = ⨆ j, globalFoxBlock P generators (localWords j) := by
  apply le_antisymm
  · rw [foxKernel_eq_completedRelationModule P generators relations hP hgen hpresentation]
    exact completedRelationModule_restrict_le_blocks_of_rowCoverage P generators κs localWords relations hcover
  · apply iSup_le
    intro j
    exact globalFoxBlock_le_kernel P generators (localWords j)

/-- The literal family of substituted completed local relations. -/
def substitutedRelationFamily (localRelations : ∀ j, Set (CompletedWords (κs j))) :
    Set (CompletedWords ι) :=
  {r | ∃ (j : J) (s : CompletedWords (κs j)), s ∈ localRelations j ∧
    completedSubstitution (localWords j) s = r}

/-- Actual local finite-group relation identities imply coverage of the
corresponding entire substituted relation family. -/
theorem substitutedRelationFamily_coverage
    (D : J → Type u) [∀ j, Group (D j)] [∀ j, Finite (D j)]
    (localGenerators : ∀ j, κs j → D j) (localMaps : ∀ j, D j →* P)
    (hwords : ∀ j i, FreeGroup.lift generators (localWords j i) =
      localMaps j (localGenerators j i))
    (localRelations : ∀ j, Set (CompletedWords (κs j)))
    (hlocalRel : ∀ j s, s ∈ localRelations j →
      completedWordEvaluation (D j) (localGenerators j) s = 1) :
    CompletedRelationCoverage P generators κs localWords
      (substitutedRelationFamily κs localWords localRelations) := by
  rintro r ⟨j,s,hs,rfl⟩
  refine ⟨j,s,?_,rfl⟩
  simp_rw [hwords]
  rw [completedWordEvaluation_naturality,hlocalRel j s hs,map_one]

end UnitDistance.GroupAugmentation


namespace UnitDistance.GroupAugmentation
variable (P : Type) [Group P] [Finite P]
local notation "F" => ZMod 2
variable {ι : Type} [Fintype ι] (generators : ι → P)
variable {J : Type*} (κs : J → Type) [∀ j, Fintype (κs j)]
variable (otherWords : ∀ j, κs j → FreeGroup ι)

/-- Coverage of the original relations by the other blocks proves the
required common-row inclusion. The relation set here is explicitly the
original one; the whole completed presentation is not substituted for it. -/
theorem commonRow_le_other_blocks_of_original_coverage (hP : IsPGroup 2 P)
    (words : Fin 3 → FreeGroup ι) (f : Dyadic.D →* P)
    (hwords : ∀ j, FreeGroup.lift generators (words j) = f (Dyadic.Filtration.gen j))
    (originalRelations : Set (CompletedWords ι))
    (hrel : ∀ s ∈ originalRelations, completedWordEvaluation P generators s = 1)
    (hcover : CompletedFoxRowCoverage P generators κs otherWords originalRelations)
    (r : CompletedWords (Fin 3))
    (hr : CompletedProTwoConsequence originalRelations (completedSubstitution words r)) :
    globalDyadicRow P generators words f (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen r) ≤
      ⨆ j, globalFoxBlock P generators (otherWords j) := by
  exact (globalDyadicRow_le_relationModule_of_proTwoConsequence P generators words f hwords hP
    originalRelations hrel r hr).trans
      (completedRelationModule_restrict_le_blocks_of_rowCoverage P generators κs otherWords
        originalRelations hcover)

/-- Original pro-2 consequence and actual row equality suffice even when
the arithmetic local-generator lifts are completed words. Only the original
row module is included in the other blocks. -/
theorem commonRow_le_other_blocks_of_original_row (hP : IsPGroup 2 P)
    (words : Fin 3 → FreeGroup ι) (f : Dyadic.D →* P)
    (hwords : ∀ j, FreeGroup.lift generators (words j) = f (Dyadic.Filtration.gen j))
    (originalRelations : Set (CompletedWords ι))
    (hrel : ∀ s ∈ originalRelations, completedWordEvaluation P generators s = 1)
    (hcover : CompletedFoxRowCoverage P generators κs otherWords originalRelations)
    (localRelation : CompletedWords (Fin 3)) (globalRelation : CompletedWords ι)
    (hroweq : completedFoxDerivative P generators globalRelation =
      completedFoxDerivative P generators (completedSubstitution words localRelation))
    (hr : CompletedProTwoConsequence originalRelations globalRelation) :
    globalDyadicRow P generators words f
      (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen localRelation) ≤
      ⨆ j, globalFoxBlock P generators (otherWords j) := by
  have hm := completedFoxDerivative_mem_of_proTwoConsequence P generators hP
    originalRelations hrel globalRelation hr
  exact (globalDyadicRow_le_module_of_global_derivative P generators words f hwords
    localRelation globalRelation hroweq _ hm).trans
      (completedRelationModule_restrict_le_blocks_of_rowCoverage P generators κs otherWords
        originalRelations hcover)

end UnitDistance.GroupAugmentation
