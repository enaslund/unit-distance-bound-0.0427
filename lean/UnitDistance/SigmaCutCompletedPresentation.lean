module

public import UnitDistance.SigmaCutLocalWords
public import UnitDistance.ProTwoFiniteQuotient

@[expose] public section
set_option backward.privateInPublic true


/-! The actual cut has a completed presentation covered by finite local
blocks. Its genuine arithmetic dyadic relation is a consequence of the
nondyadic local relations, which supplies the optimized common row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace UnitDistance.ArithmeticProP.SigmaCut
open GroupAugmentation ArithmeticLocalBlocks ProCGroups ProCGroups.Presentations

/-- All actual nondyadic local relations; this set contains the six
original arithmetic relations and excludes the dyadic local block. -/
def otherRelations : Set (CompletedWords (Fin 7)) :=
  completedGeneratorRelationFamily GeneratorType otherLifts
    (completeLocalRelations GeneratorType LocalGroup ArithmeticLocalBlocks.generators)

theorem completed_local_word_map (j : AllIndex) (w : FreeGroup (AllGeneratorType j)) :
    completionMap (FiniteFreeProTwo.generator 7)
      (completedGeneratorSubstitution (allLifts j) (wordCompletion _ w))=
      FreeGroup.lift (allSource j) w := by
  rw [completionMap_generatorSubstitution]
  simp only [allLifts_map]
  rw [completionMap_word]

theorem completed_other_word_map (j : Index) (w : FreeGroup (GeneratorType j)) :
    completionMap (FiniteFreeProTwo.generator 7)
      (completedGeneratorSubstitution (otherLifts j) (wordCompletion _ w))=
      FreeGroup.lift (otherSource j) w :=
  completed_local_word_map (some j) w

theorem original_mem_other_image (i : Fin 6) :
    (sigmaOriginalRelator i : Source)∈
      completionMap (FiniteFreeProTwo.generator 7) '' otherRelations := by
  let w := originalLocalWords i
  refine ⟨completedGeneratorSubstitution (otherLifts w.1) (wordCompletion _ w.2),?_,?_⟩
  · refine ⟨w.1,wordCompletion _ w.2,?_,rfl⟩
    change completedWordEvaluation _ _ (wordCompletion _ w.2)=1
    rw [completedWordEvaluation_word]
    exact originalLocalWords_vanish i
  · rw [completed_other_word_map]
    exact originalLocalWords_source i

/-- The genuine local arithmetic relation is a finite-two consequence of
actual relations in the nondyadic blocks. -/
theorem genuine_other_consequence
    (hgen : closedNormalClosure (Set.range (fun i↦(sigmaOriginalRelator i : Source)))=
      (sigmaRelationKernel : Subgroup Source)) :
    CompletedProTwoConsequence otherRelations SigmaDyadic.completedGlobalRelation := by
  apply completedProTwoConsequence_of_normalClosure (FiniteFreeProTwo.generator 7)
    (FiniteFreeProTwo.isFree 7)
  have hle : (sigmaRelationKernel : Subgroup Source)≤
      closedNormalClosure (completionMap (FiniteFreeProTwo.generator 7) '' otherRelations) := by
    rw [←hgen]
    apply closedNormalClosure_le_closed_normal (closedNormalClosure_isClosed _)
    rintro _ ⟨i,rfl⟩
    exact subset_closedNormalClosure _ (original_mem_other_image i)
  apply hle
  change sigmaFreeMap (completionMap (FiniteFreeProTwo.generator 7)
    SigmaDyadic.completedGlobalRelation)=1
  exact SigmaDyadic.completedGlobalRelation_killed

section Finite
variable [Finite ActualQuotient]

/-- The actual quotient map, with the canonical finite-group topology. -/
def finiteProjection : Source →ₜ* ProfiniteGrp.ofFiniteGrp (FiniteGrp.of ActualQuotient) where
  toMonoidHom := (projection actualExtra).toMonoidHom
  continuous_toFun := by
    have hi : @Continuous ActualQuotient
        (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of ActualQuotient))
        (inferInstance : TopologicalSpace ActualQuotient)
        (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of ActualQuotient)).toProfinite.toTop.str
        (fun p=>p) := continuous_of_discreteTopology
    exact hi.comp (projection actualExtra).continuous

def finiteGenerators : Fin 7 → ActualQuotient :=
  fun i=>projection actualExtra (FiniteFreeProTwo.generator 7 i)

theorem finiteProjection_kernel : finiteProjection.toMonoidHom.ker=kernel actualExtra := by
  ext g
  exact QuotientGroup.eq_one_iff g

theorem finite_isTwoGroup : IsPGroup 2 ActualQuotient :=
  isPGroup_of_freeProTwo_surjective (FiniteFreeProTwo.generator 7) (FiniteFreeProTwo.isFree 7)
    (projection actualExtra) (projection_surjective actualExtra)

theorem finite_generates : Subgroup.closure (Set.range finiteGenerators)=⊤ :=
  generates_of_freeProTwo_surjective (FiniteFreeProTwo.generator 7) (FiniteFreeProTwo.isFree 7)
    (projection actualExtra) (projection_surjective actualExtra)

theorem finite_allLifts (hgen : ArithmeticPresentation) (j : AllIndex) (i : AllGeneratorType j) :
    completedWordEvaluation ActualQuotient finiteGenerators (allLifts j i)=
      allMap hgen j (allGenerators j i) := by
  rw [allMap_generator]
  change completedWordEvaluation ActualQuotient
    (fun i=>finiteProjection (FiniteFreeProTwo.generator 7 i)) (allLifts j i)=_
  rw [completedWordEvaluation_completionMap,allLifts_map]
  rfl

theorem finite_otherLifts (j : Index) (i : GeneratorType j) :
    completedWordEvaluation ActualQuotient finiteGenerators (otherLifts j i)=
      otherMap j (ArithmeticLocalBlocks.generators j i) := by
  rw [otherMap_generator]
  change completedWordEvaluation ActualQuotient
    (fun i=>finiteProjection (FiniteFreeProTwo.generator 7 i)) (otherLifts j i)=_
  rw [completedWordEvaluation_completionMap]
  change finiteProjection (completionMap (FiniteFreeProTwo.generator 7)
    (SigmaDyadic.completedLift 7 (otherSource j i)))=_
  rw [SigmaDyadic.completedLift_map]
  rfl

/-- Full actual finite-two presentation from all twelve local blocks. -/
theorem finite_completedPresentation (hgen : ArithmeticPresentation) :
    CompletedProTwoPresentation ActualQuotient finiteGenerators allRelations := by
  apply completedPresentation_of_local_cover AllGeneratorType allGroup allGenerators
    (FiniteFreeProTwo.generator 7) ActualQuotient finiteProjection (allMap hgen) allLifts
    (FiniteFreeProTwo.isFree 7) (relations actualExtra) finiteProjection_kernel
    (finite_allLifts hgen)
  intro s hs
  obtain ⟨w,hw,he⟩ := cut_local_word_cover s hs
  refine ⟨w.1,wordCompletion _ w.2,?_,?_⟩
  · rw [completedWordEvaluation_word]
    exact hw
  · rw [completed_local_word_map]
    exact he

end Finite
end UnitDistance.ArithmeticProP.SigmaCut
