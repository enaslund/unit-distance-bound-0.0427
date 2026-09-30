module

public import UnitDistance.Sqrt241.Cut.LocalWords
public import UnitDistance.ProTwoFiniteQuotient
public import UnitDistance.DyadicGenuineFoxInitial
public import UnitDistance.ProTwoCompletedSubstitution

@[expose] public section
set_option backward.privateInPublic true


/-!
# Completed presentation of a finite cut quotient; the genuine consequence

* The completed genuine relation (local half of `SigmaDyadicCompletedRelation`,
  with the genuine local relation `r` as a parameter): its evaluation in `D`
  is trivial and its first Fox row is the proved dyadic initial.
* Every relator lies in the image of the relations of the blocks other than
  `𝔭₁`; with the presentation hypothesis the lifted genuine relation at `𝔭₁`
  is therefore a completed pro-2 consequence of those relations.
* If the cut quotient is finite, the relations of all blocks give its
  completed pro-2 presentation (`finite_completedPresentation`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.Cut
open GroupAugmentation ProCGroups ProCGroups.ProC ProCGroups.Presentations GroupData

/-- Completed lift of a local relation. -/
def completedABC (r : LocalSource) : CompletedWords (Fin 3) := completedLift 3 r

theorem completedABC_detector (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation) :
    completedFiniteMap FreeThreeQuadratic.Q FreeThreeQuadratic.wordDetector (completedABC r) =
      FreeThreeQuadratic.relation := by
  let π : LocalSource →ₜ* ProfiniteGrp.ofFiniteGrp (FiniteGrp.of FreeThreeQuadratic.Q) :=
    ⟨PadicTwoQuadraticRelation.detector.toMonoidHom,
      PadicTwoQuadraticRelation.detector.continuous⟩
  have he : π.toMonoidHom.comp (FreeGroup.lift (FiniteFreeProTwo.generator 3)) =
      FreeThreeQuadratic.wordDetector := by
    apply FreeGroup.ext_hom
    intro i
    change PadicTwoQuadraticRelation.detector
      (FreeGroup.lift (FiniteFreeProTwo.generator 3) (FreeGroup.of i)) =
      FreeGroup.lift FreeThreeQuadratic.basis (FreeGroup.of i)
    rw [FreeGroup.lift_apply_of,FreeGroup.lift_apply_of]
    exact PadicTwoQuadraticRelation.detector_generator i
  have h := finiteMap_comp_completionMap (FiniteFreeProTwo.generator 3)
    FreeThreeQuadratic.Q π (completedABC r)
  rw [he] at h
  rw [← h]
  change PadicTwoQuadraticRelation.detector
    (completionMap (FiniteFreeProTwo.generator 3) (completedLift 3 r)) = _
  rw [completedLift_map]
  exact hr

/-- The completed genuine relation in the `x = b, y = a, z = a c` coordinates. -/
def completedRelation (r : LocalSource) : CompletedWords (Fin 3) :=
  completedSubstitution Dyadic.GenuineFox.inverseWords (completedABC r)

theorem completedRelation_initial (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation) :
    completedWordEvaluation Dyadic.D Dyadic.Filtration.gen (completedRelation r) = 1 ∧
      ∀ i, completedFoxDerivative Dyadic.D Dyadic.Filtration.gen (completedRelation r) i -
        Dyadic.AlgebraD.linearFoxCoefficients i ∈ Dyadic.AlgebraD.augmentationPower 2 :=
  Dyadic.GenuineFox.completed_initial (completedABC r) (completedABC_detector r hr)

theorem inverseWords_localXYZ :
    (fun i => FreeGroup.lift SourceLifts.localXYZ (Dyadic.GenuineFox.inverseWords i)) =
      FiniteFreeProTwo.generator 3 := by
  funext i
  fin_cases i <;> simp [SourceLifts.localXYZ,Dyadic.GenuineFox.inverseWords,
    Dyadic.ArithmeticPresentation.x,Dyadic.ArithmeticPresentation.y,
    Dyadic.ArithmeticPresentation.z]

theorem completedRelation_local (r : LocalSource) :
    completionMap SourceLifts.localXYZ (completedRelation r) = r := by
  rw [completedRelation,completionMap_substitution,inverseWords_localXYZ]
  exact completedLift_map 3 r

namespace SourceLifts
variable (A : SourceLifts)

/-- The completed lift of the genuine relation at `𝔭_P`. -/
def completedGlobalRelation (r : LocalSource) (P : Fin 2) : CompletedWords (Fin 8) :=
  completedGeneratorSubstitution (fun i => completedLift 8 (A.dyadicXYZ P i)) (completedRelation r)

theorem completedGlobalRelation_free (r : LocalSource) (P : Fin 2) :
    completionMap (FiniteFreeProTwo.generator 8) (A.completedGlobalRelation r P) =
      A.dyadic P r := by
  rw [completedGlobalRelation,completionMap_generatorSubstitution]
  simp only [completedLift_map]
  have he : (fun i => A.dyadicXYZ P i) = fun i => A.dyadic P (localXYZ i) :=
    funext (A.dyadicXYZ_eq P)
  rw [he,← completionMap_comp_continuous localXYZ (A.dyadic P),completedRelation_local]

theorem allLifts_none : A.allLifts none = fun i => completedLift 8 (A.dyadicXYZ 0 i) := rfl

/-- Each of the seven relators is the image of a relation of a block other than `𝔭₁`. -/
theorem relator_mem_other_image (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation) (i : Fin 7) :
    A.relators r i ∈ completionMap (FiniteFreeProTwo.generator 8) '' A.otherRelations := by
  by_cases hi : i.val < 6
  · let w := relatorLocalWords ⟨i.val,hi⟩
    refine ⟨completedGeneratorSubstitution (A.otherLifts w.1) (wordCompletion _ w.2),?_,?_⟩
    · refine ⟨w.1,wordCompletion _ w.2,?_,rfl⟩
      change completedWordEvaluation _ _ (wordCompletion _ w.2) = 1
      rw [completedWordEvaluation_word]
      exact relatorLocalWords_vanish ⟨i.val,hi⟩
    · rw [completionMap_generatorSubstitution]
      have hl : (fun k => completionMap (FiniteFreeProTwo.generator 8) (A.otherLifts w.1 k)) =
          A.otherSource w.1 := funext fun k => completedLift_map 8 _
      rw [hl,completionMap_word]
      exact (A.relatorLocalWords_source r ⟨i.val,hi⟩)
  · have hi6 : i = 6 := by omega
    subst hi6
    refine ⟨A.completedGlobalRelation r 1,⟨.inr (.inr (.inl ())),completedRelation r,
      (completedRelation_initial r hr).1,rfl⟩,?_⟩
    exact A.completedGlobalRelation_free r 1

/-- With the presentation hypothesis, the genuine relation at `𝔭₁` is a completed
pro-2 consequence of the relations of the other blocks. -/
theorem genuine_other_consequence (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) :
    CompletedProTwoConsequence A.otherRelations (A.completedGlobalRelation r 0) := by
  apply completedProTwoConsequence_of_normalClosure (FiniteFreeProTwo.generator 8)
    (FiniteFreeProTwo.isFree 8)
  rw [A.completedGlobalRelation_free r 0]
  have hle : closedNormalClosure (Set.range (A.relators r)) ≤
      closedNormalClosure (completionMap (FiniteFreeProTwo.generator 8) '' A.otherRelations) := by
    apply closedNormalClosure_le_closed_normal (closedNormalClosure_isClosed _)
    rintro _ ⟨i,rfl⟩
    exact subset_closedNormalClosure _ (A.relator_mem_other_image r hr i)
  exact hle hgen

theorem completed_local_word_map (j : AllIndex) (w : FreeGroup (AllGeneratorType j)) :
    completionMap (FiniteFreeProTwo.generator 8)
      (completedGeneratorSubstitution (A.allLifts j) (wordCompletion _ w)) =
      FreeGroup.lift (A.allSource j) w := by
  rw [completionMap_generatorSubstitution]
  simp only [A.allLifts_map]
  rw [completionMap_word]

section Finite
variable [Finite A.ActualQuotient]

/-- The quotient map, with the finite-group topology. -/
def finiteProjection :
    Source →ₜ* ProfiniteGrp.ofFiniteGrp (FiniteGrp.of A.ActualQuotient) where
  toMonoidHom := A.projection.toMonoidHom
  continuous_toFun := by
    have hi : @Continuous A.ActualQuotient
        (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of A.ActualQuotient))
        (inferInstance : TopologicalSpace A.ActualQuotient)
        (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of A.ActualQuotient)).toProfinite.toTop.str
        (fun p => p) := continuous_of_discreteTopology
    exact hi.comp A.projection.continuous

def finiteGenerators : Fin 8 → A.ActualQuotient :=
  fun i => A.projection (FiniteFreeProTwo.generator 8 i)

theorem finiteProjection_kernel : A.finiteProjection.toMonoidHom.ker = A.kernel := by
  ext g
  exact QuotientGroup.eq_one_iff g

theorem finite_isTwoGroup : IsPGroup 2 A.ActualQuotient :=
  isPGroup_of_freeProTwo_surjective (FiniteFreeProTwo.generator 8) (FiniteFreeProTwo.isFree 8)
    A.projection A.projection_surjective

theorem finite_generates : Subgroup.closure (Set.range A.finiteGenerators) = ⊤ :=
  generates_of_freeProTwo_surjective (FiniteFreeProTwo.generator 8) (FiniteFreeProTwo.isFree 8)
    A.projection A.projection_surjective

variable (r : LocalSource) (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
  (hgen : A.Presentation r)

theorem finite_allLifts (j : AllIndex) (i : AllGeneratorType j) :
    completedWordEvaluation A.ActualQuotient A.finiteGenerators (A.allLifts j i) =
      A.allMap r hr hgen j (allGenerators j i) := by
  rw [allMap_generator]
  change completedWordEvaluation A.ActualQuotient
    (fun i => A.finiteProjection (FiniteFreeProTwo.generator 8 i)) (A.allLifts j i) = _
  rw [completedWordEvaluation_completionMap,allLifts_map]
  rfl

theorem finite_otherLifts (j : Index) (i : GeneratorType j) :
    completedWordEvaluation A.ActualQuotient A.finiteGenerators (A.otherLifts j i) =
      A.otherMap r hr hgen j (localGenerators j i) :=
  A.finite_allLifts r hr hgen (some j) i

include hr hgen in
/-- The relations of all local blocks present the finite cut quotient. -/
theorem finite_completedPresentation :
    CompletedProTwoPresentation A.ActualQuotient A.finiteGenerators A.allRelations := by
  apply completedPresentation_of_local_cover AllGeneratorType allGroup allGenerators
    (FiniteFreeProTwo.generator 8) A.ActualQuotient A.finiteProjection (A.allMap r hr hgen)
    A.allLifts (FiniteFreeProTwo.isFree 8) A.lifts.words A.finiteProjection_kernel
    (A.finite_allLifts r hr hgen)
  intro s hs
  obtain ⟨w,hw,he⟩ := A.cut_local_word_cover s hs
  refine ⟨w.1,wordCompletion _ w.2,?_,?_⟩
  · rw [completedWordEvaluation_word]
    exact hw
  · rw [completed_local_word_map]
    exact he

end Finite
end SourceLifts
end UnitDistance.Sqrt241.Cut
