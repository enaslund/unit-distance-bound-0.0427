module

public import UnitDistance.ProTwoCompletedSubstitution

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite local groups give a completed Fox presentation once their
literal local relations cover the defining closed normal generators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.GroupAugmentation
open ProCGroups ProCGroups.ProC ProCGroups.FreeProC ProCGroups.Presentations
variable {ι G : Type} [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Finite evaluated completed words agree with actual profinite evaluation. -/
theorem completedWordEvaluation_completionMap (x : ι → G)
    (P : Type) [Group P] [Finite P]
    (π : G →ₜ* ProfiniteGrp.ofFiniteGrp (FiniteGrp.of P)) (r : CompletedWords ι) :
    completedWordEvaluation P (fun i=>π (x i)) r=π (completionMap x r) := by
  rw [completedWordEvaluation_eq_finiteMap,finiteMap_comp_completionMap]
  have he : FreeGroup.lift (fun i=>π (x i))=π.toMonoidHom.comp (FreeGroup.lift x) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  erw [he]

theorem completedWordEvaluation_substitution
    {κ : Type} [Fintype κ] [TopologicalSpace κ] [DiscreteTopology κ] (P : Type) [Group P] [Finite P]
    (y : ι → P) (words : κ → FreeGroup ι) (r : CompletedWords κ) :
    completedWordEvaluation P y (completedSubstitution words r)=
      completedWordEvaluation P (fun j=>FreeGroup.lift y (words j)) r := by
  rw [completedWordEvaluation_eq_finiteMap,completedFiniteMap_substitution,
    completedWordEvaluation_eq_finiteMap]
  have he : (FreeGroup.lift y).comp (FreeGroup.lift words)=
      FreeGroup.lift (fun j=>FreeGroup.lift y (words j)) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  erw [he]

variable {J : Type} (κs : J → Type) [∀j,Fintype (κs j)]
  (D : J → Type) [∀j,Group (D j)] [∀j,Finite (D j)]
  (localGenerators : ∀j,κs j → D j)

/-- All actual completed relations of each specified finite local group. -/
def completeLocalRelations (j : J) : Set (CompletedWords (κs j)) :=
  {r | completedWordEvaluation (D j) (localGenerators j) r=1}

variable (x : ι → G) (P : Type) [Group P] [Finite P]
  (π : G →ₜ* ProfiniteGrp.ofFiniteGrp (FiniteGrp.of P))
  (localMaps : ∀j,D j →* P) (lifts : ∀j,κs j → CompletedWords ι)

theorem localFamily_image_le_kernel
    (hlifts : ∀j i,completedWordEvaluation P (fun i=>π (x i)) (lifts j i)=
      localMaps j (localGenerators j i)) :
    completionMap x '' completedGeneratorRelationFamily κs lifts
      (completeLocalRelations κs D localGenerators) ⊆ π.toMonoidHom.ker := by
  rintro _ ⟨_,⟨j,r,hr,rfl⟩,rfl⟩
  change π (completionMap x (completedGeneratorSubstitution (lifts j) r))=1
  rw [←completedWordEvaluation_completionMap]
  have he := exists_literal_affine_lifts P (fun i=>π (x i)) (lifts j)
  obtain ⟨words,hw⟩ := he
  have hv := literal_affine_lifts_evaluation P (fun i=>π (x i)) (lifts j) words hw
  have ha := completedGeneratorSubstitution_affine_eq P (fun i=>π (x i))
    (lifts j) words hw r
  have hright := congrArg (fun a : FoxAffine (ZMod 2) P (ι := ι)=>a.right) ha
  change completedWordEvaluation P (fun i=>π (x i))
    (completedGeneratorSubstitution (lifts j) r)=
      completedWordEvaluation P (fun i=>π (x i)) (completedSubstitution words r) at hright
  letI : TopologicalSpace (κs j) := ⊥
  letI : DiscreteTopology (κs j) := ⟨rfl⟩
  rw [hright,completedWordEvaluation_substitution]
  have hwords : (fun k=>FreeGroup.lift (fun i=>π (x i)) (words k))=
      fun k=>localMaps j (localGenerators j k) := by
    funext k
    exact (hv k).trans (hlifts j k)
  erw [hwords,completedWordEvaluation_naturality,hr,map_one]

/-- A proved finite quotient presentation follows from actual local
relation coverage of the defining closed normal generators. -/
theorem completedPresentation_of_local_cover
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (S : Set G) (hkernel : π.toMonoidHom.ker=closedNormalClosure S)
    (hlifts : ∀j i,completedWordEvaluation P (fun i=>π (x i)) (lifts j i)=
      localMaps j (localGenerators j i))
    (hcover : ∀s∈S,∃(j : J) (r : CompletedWords (κs j)),
      completedWordEvaluation (D j) (localGenerators j) r=1 ∧
      completionMap x (completedGeneratorSubstitution (lifts j) r)=s) :
    CompletedProTwoPresentation P (fun i=>π (x i))
      (completedGeneratorRelationFamily κs lifts (completeLocalRelations κs D localGenerators)) := by
  apply completedProTwoPresentation_of_closed_kernel x hfree P π
  apply le_antisymm
  · rw [hkernel]
    apply closedNormalClosure_le_closed_normal (closedNormalClosure_isClosed _)
    intro s hs
    obtain ⟨j,r,hr,he⟩ := hcover s hs
    exact subset_closedNormalClosure _
      ⟨completedGeneratorSubstitution (lifts j) r,⟨j,r,hr,rfl⟩,he⟩
  · apply closedNormalClosure_le_closed_normal (ProCGroups.ContinuousMonoidHom.isClosed_ker π)
    exact localFamily_image_le_kernel κs D localGenerators x P π localMaps lifts hlifts

end UnitDistance.GroupAugmentation
