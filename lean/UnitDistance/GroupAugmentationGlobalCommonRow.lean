module

public import UnitDistance.GroupAugmentationGlobalBlocks
public import UnitDistance.GroupAugmentationCompletedRelations
public import UnitDistance.GroupAugmentationCompletedSubstitution
public import UnitDistance.GroupAugmentationFoxNaturality

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual completed dyadic row is a global common submodule

The completed local relation evaluates to one in the local dyadic group.
Its substituted completed global word belongs to the closed normal closure
of the original global relations. The proved chain rule and continuity then
place its entire actual row image in both global relation blocks.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (P : Type) [Group P] [Finite P]
local notation "F" => ZMod 2
variable {ι : Type} [Fintype ι]
variable (generators : ι → P) (words : Fin 3 → FreeGroup ι) (f : Dyadic.D →* P)
variable (hwords : ∀ j, FreeGroup.lift generators (words j) = f (Dyadic.Filtration.gen j))

include hwords in
/-- The induced actual local row is exactly the completed local derivative
with ambient evaluation. -/
theorem dyadic_completed_row_naturality (r : CompletedWords (Fin 3)) :
    (fun i => induced F Dyadic.D f
      (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen r i)) =
    completedFoxDerivative P (fun j => FreeGroup.lift generators (words j)) r := by
  funext i
  simp_rw [hwords]
  exact (completedFoxDerivative_naturality Dyadic.D P Dyadic.Filtration.gen f r i).symm

include hwords in
/-- An actual local completed relation gives an actual local augmentation
kernel row after induction into the ambient group algebra. -/
theorem dyadic_completed_row_kernel (r : CompletedWords (Fin 3))
    (hr : completedWordEvaluation Dyadic.D Dyadic.Filtration.gen r = 1) :
    foxMap F P (fun j => FreeGroup.lift generators (words j))
      (fun i => induced F Dyadic.D f
        (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen r i)) = 0 := by
  have he := congrArg (induced F Dyadic.D f)
    (completedFoxDerivative_fundamental Dyadic.D Dyadic.Filtration.gen r)
  rw [hr,delta_one,sub_self,map_zero] at he
  simp only [foxMap,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_mul,map_sub,
    induced_delta,map_one] at he
  simp_rw [hwords]
  exact he

include hwords in
/-- Closed normal consequence in the original presentation places the full
actual induced row image inside the original global relation module. -/
theorem globalDyadicRow_le_completedRelationModule
    (relations : Set (CompletedWords ι))
    (hrel : ∀ s ∈ relations, completedWordEvaluation P generators s = 1)
    (r : CompletedWords (Fin 3))
    (hr : completedSubstitution words r ∈ (Subgroup.normalClosure relations).topologicalClosure) :
    globalDyadicRow P generators words f (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen r) ≤
      (completedFoxRelationModule P generators relations).restrictScalars F := by
  rintro a ⟨b,⟨q,rfl⟩,rfl⟩
  change foxSubstitutionAlgebra F P generators words
    (q • (fun i => induced F Dyadic.D f
      (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen r i))) ∈
    completedFoxRelationModule P generators relations
  rw [map_smul]
  apply Submodule.smul_mem
  rw [dyadic_completed_row_naturality P generators words f hwords r]
  change foxSubstitution F P generators words
    (completedFoxDerivative P (fun j => FreeGroup.lift generators (words j)) r) ∈ _
  rw [← completedFoxDerivative_substitution words P generators r]
  exact completedFoxDerivative_mem_of_closed_normalClosure P generators relations hrel
    (completedSubstitution words r) hr

include hwords in
/-- The common-row inclusion is proved in the actual global coefficient
module, with both sides independently defined before the Hilbert estimate. -/
theorem globalDyadicRow_le_intersection
    (relations : Set (CompletedWords ι))
    (hrel : ∀ s ∈ relations, completedWordEvaluation P generators s = 1)
    (r : CompletedWords (Fin 3))
    (hrlocal : completedWordEvaluation Dyadic.D Dyadic.Filtration.gen r = 1)
    (hrglobal : completedSubstitution words r ∈
      (Subgroup.normalClosure relations).topologicalClosure) :
    globalDyadicRow P generators words f (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen r) ≤
      (completedFoxRelationModule P generators relations).restrictScalars F ⊓
        globalFoxBlock P generators words := by
  exact le_inf
    (globalDyadicRow_le_completedRelationModule P generators words f hwords relations hrel r hrglobal)
    (globalDyadicRow_le_block P generators words f _
      (dyadic_completed_row_kernel P generators words f hwords r hrlocal))

include hwords in
/-- The weaker and arithmetic-relevant finite-2 consequence condition also
places the full actual row image in the original global relation module. -/
theorem globalDyadicRow_le_relationModule_of_proTwoConsequence (hP : IsPGroup 2 P)
    (relations : Set (CompletedWords ι))
    (hrel : ∀ s ∈ relations, completedWordEvaluation P generators s = 1)
    (r : CompletedWords (Fin 3))
    (hr : CompletedProTwoConsequence relations (completedSubstitution words r)) :
    globalDyadicRow P generators words f (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen r) ≤
      (completedFoxRelationModule P generators relations).restrictScalars F := by
  rintro a ⟨b,⟨q,rfl⟩,rfl⟩
  change foxSubstitutionAlgebra F P generators words
    (q • (fun i => induced F Dyadic.D f
      (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen r i))) ∈
    completedFoxRelationModule P generators relations
  rw [map_smul]
  apply Submodule.smul_mem
  rw [dyadic_completed_row_naturality P generators words f hwords r]
  change foxSubstitution F P generators words
    (completedFoxDerivative P (fun j => FreeGroup.lift generators (words j)) r) ∈ _
  rw [← completedFoxDerivative_substitution words P generators r]
  exact completedFoxDerivative_mem_of_proTwoConsequence P generators hP relations hrel
    (completedSubstitution words r) hr

include hwords in
/-- Actual common-row inclusion under pro-2 consequence, proved using the
finite affine 2-group test rather than a full-profinite closure hypothesis. -/
theorem globalDyadicRow_le_intersection_of_proTwoConsequence (hP : IsPGroup 2 P)
    (relations : Set (CompletedWords ι))
    (hrel : ∀ s ∈ relations, completedWordEvaluation P generators s = 1)
    (r : CompletedWords (Fin 3))
    (hrlocal : completedWordEvaluation Dyadic.D Dyadic.Filtration.gen r = 1)
    (hrglobal : CompletedProTwoConsequence relations (completedSubstitution words r)) :
    globalDyadicRow P generators words f (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen r) ≤
      (completedFoxRelationModule P generators relations).restrictScalars F ⊓
        globalFoxBlock P generators words := by
  exact le_inf
    (globalDyadicRow_le_relationModule_of_proTwoConsequence P generators words f hwords hP
      relations hrel r hrglobal)
    (globalDyadicRow_le_block P generators words f _
      (dyadic_completed_row_kernel P generators words f hwords r hrlocal))

include hwords in
/-- The common-row inclusion depends only on the actual global derivative
of the completed consequence. Thus literal affine representatives need not
preserve the completed word itself or its pro-2 normal-consequence class. -/
theorem globalDyadicRow_le_module_of_global_derivative
    (localRelation : CompletedWords (Fin 3)) (globalRelation : CompletedWords ι)
    (hroweq : completedFoxDerivative P generators globalRelation =
      completedFoxDerivative P generators (completedSubstitution words localRelation))
    (M : Submodule (A F P) (ι → A F P))
    (hmem : completedFoxDerivative P generators globalRelation ∈ M) :
    globalDyadicRow P generators words f
      (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen localRelation) ≤ M.restrictScalars F := by
  rintro a ⟨b,⟨q,rfl⟩,rfl⟩
  change foxSubstitutionAlgebra F P generators words
    (q • (fun i => induced F Dyadic.D f
      (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen localRelation i))) ∈ M
  rw [map_smul]
  apply M.smul_mem
  rw [dyadic_completed_row_naturality P generators words f hwords localRelation]
  change foxSubstitution F P generators words
    (completedFoxDerivative P (fun j => FreeGroup.lift generators (words j)) localRelation) ∈ M
  rw [← completedFoxDerivative_substitution words P generators localRelation,← hroweq]
  exact hmem

end UnitDistance.GroupAugmentation
