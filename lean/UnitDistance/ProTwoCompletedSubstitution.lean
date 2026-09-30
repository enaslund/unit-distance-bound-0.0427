module

public import UnitDistance.ProTwoCompletedConsequence
public import UnitDistance.GroupAugmentationCompletedGeneratorLifts

@[expose] public section
set_option backward.privateInPublic true


/-! Actual profinite evaluation commutes with literal and completed
substitution, including targets that are infinite. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace UnitDistance.GroupAugmentation
variable {ι κ G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem completionMap_substitution (x : ι → G) (words : κ → FreeGroup ι)
    (r : CompletedWords κ) :
    completionMap x (completedSubstitution words r)=
      completionMap (fun i=>FreeGroup.lift x (words i)) r := by
  have he : (fun r=>completionMap x (completedSubstitution words r))=
      fun r=>completionMap (fun i=>FreeGroup.lift x (words i)) r := by
    apply (ProfiniteGrp.ProfiniteCompletion.denseRange
      (G := GrpCat.of (FreeGroup κ))).equalizer
      ((completionMap x).continuous.comp (completedSubstitution words).hom.continuous)
      (completionMap _).continuous
    funext w
    change completionMap x (completedSubstitution words (wordCompletion κ w))=
      completionMap (fun i=>FreeGroup.lift x (words i)) (wordCompletion κ w)
    rw [completedSubstitution_word,completionMap_word,completionMap_word]
    have hh : (FreeGroup.lift x).comp (FreeGroup.lift words)=
        FreeGroup.lift (fun i=>FreeGroup.lift x (words i)) := by
      apply FreeGroup.ext_hom
      intro i
      simp
    exact DFunLike.congr_fun hh w
  exact congrFun he r

theorem completionMap_generatorSubstitution (x : ι → G) (lifts : κ → CompletedWords ι)
    (r : CompletedWords κ) :
    completionMap x (completedGeneratorSubstitution lifts r)=
      completionMap (fun i=>completionMap x (lifts i)) r := by
  have he : (fun r=>completionMap x (completedGeneratorSubstitution lifts r))=
      fun r=>completionMap (fun i=>completionMap x (lifts i)) r := by
    apply (ProfiniteGrp.ProfiniteCompletion.denseRange
      (G := GrpCat.of (FreeGroup κ))).equalizer
      ((completionMap x).continuous.comp (completedGeneratorSubstitution lifts).hom.continuous)
      (completionMap _).continuous
    funext w
    change completionMap x (completedGeneratorSubstitution lifts (wordCompletion κ w))=
      completionMap (fun i=>completionMap x (lifts i)) (wordCompletion κ w)
    rw [completedGeneratorSubstitution_word,completionMap_word]
    have hh : (completionMap x).toMonoidHom.comp (FreeGroup.lift lifts)=
        FreeGroup.lift (fun i=>completionMap x (lifts i)) := by
      apply FreeGroup.ext_hom
      intro i
      simp
    exact DFunLike.congr_fun hh w
  exact congrFun he r

theorem completionMap_comp_continuous
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (x : ι → G) (f : G →ₜ* H) (r : CompletedWords ι) :
    f (completionMap x r)=completionMap (fun i=>f (x i)) r := by
  have he : (fun r=>f (completionMap x r))=fun r=>completionMap (fun i=>f (x i)) r := by
    apply (ProfiniteGrp.ProfiniteCompletion.denseRange
      (G := GrpCat.of (FreeGroup ι))).equalizer
      (f.continuous.comp (completionMap x).continuous) (completionMap _).continuous
    funext w
    change f (completionMap x (wordCompletion ι w))=
      completionMap (fun i=>f (x i)) (wordCompletion ι w)
    rw [completionMap_word,completionMap_word]
    have hh : f.toMonoidHom.comp (FreeGroup.lift x)=FreeGroup.lift (fun i=>f (x i)) := by
      apply FreeGroup.ext_hom
      intro i
      simp
    exact DFunLike.congr_fun hh w
  exact congrFun he r

end UnitDistance.GroupAugmentation
