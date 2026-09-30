module

public import UnitDistance.GroupAugmentationCompletedRelations
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.FreeProC.Basic
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Presentations.Profinite

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual free pro-two sources and completed Fox consequences

The full profinite completion of ordinary words maps onto an actual free
pro-two source. Every finite two-group evaluation factors through that
source. Its closed normal consequences therefore satisfy the finite tests
used by the completed Fox theory.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace UnitDistance.GroupAugmentation

open ProCGroups ProCGroups.ProC ProCGroups.FreeProC ProCGroups.Presentations

variable {ι G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The actual continuous evaluation of all profinite words in a profinite
group, extending the literal ordinary free-word evaluation. -/
def completionMap (x : ι → G) : CompletedWords ι →ₜ* G :=
  (ProfiniteGrp.ProfiniteCompletion.lift (P := ProfiniteGrp.of G)
    (GrpCat.ofHom (FreeGroup.lift x))).hom

@[simp] theorem completionMap_word (x : ι → G) (w : FreeGroup ι) :
    completionMap x (wordCompletion ι w) = FreeGroup.lift x w := by
  have h := ProfiniteGrp.ProfiniteCompletion.lift_eta
    (P := ProfiniteGrp.of G) (GrpCat.ofHom (FreeGroup.lift x))
  exact ConcreteCategory.congr_hom h w

@[simp] theorem completionMap_generator (x : ι → G) (i : ι) :
    completionMap x (wordCompletion ι (FreeGroup.of i)) = x i := by
  rw [completionMap_word, FreeGroup.lift_apply_of]

variable [TopologicalSpace ι] [DiscreteTopology ι]

/-- Topological generation makes the actual completion map surjective. -/
theorem completionMap_surjective (x : ι → G)
    (hgen : Generation.TopologicallyGenerates (Set.range x)) :
    Function.Surjective (completionMap x) := by
  have hc : IsClosed ((completionMap x).toMonoidHom.range : Set G) :=
    (isCompact_range (completionMap x).continuous_toFun).isClosed
  have hr : Subgroup.closure (Set.range x) ≤ (completionMap x).toMonoidHom.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨wordCompletion ι (FreeGroup.of i), completionMap_generator x i⟩
  have ht := Subgroup.topologicalClosure_minimal _ hr hc
  rw [hgen] at ht
  intro g
  exact ht (show g ∈ (⊤ : Subgroup G) from trivial)

private theorem finiteTarget_two_basis
    (Q : Type) [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) :
    HasPGroupOpenNormalBasis 2 (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of Q)) := by
  apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  have hQ' : IsPGroup 2 (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of Q)) := hQ
  exact ⟨inferInstance, hQ'.of_surjective (QuotientGroup.mk' U.toSubgroup)
    (QuotientGroup.mk'_surjective U.toSubgroup)⟩

/-- Every finite two-group evaluation factors through the actual free
pro-two source and agrees on every completed word. -/
theorem exists_finite_evaluation_factor (x : ι → G)
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (Q : Type) [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (f : FreeGroup ι →* Q) :
    ∃ ψ : G →ₜ* ProfiniteGrp.ofFiniteGrp (FiniteGrp.of Q),
      ∀ r : CompletedWords ι, ψ (completionMap x r) = completedFiniteMap Q f r := by
  let ψ := hfree.liftHom (finiteTarget_two_basis Q hQ)
    (fun i ↦ f (FreeGroup.of i)) continuous_of_discreteTopology
  have hword : ψ.toMonoidHom.comp (FreeGroup.lift x) = f := by
    apply FreeGroup.lift.symm.injective
    funext i
    change ψ (FreeGroup.lift x (FreeGroup.of i)) = f (FreeGroup.of i)
    rw [FreeGroup.lift_apply_of]
    exact hfree.liftHom_apply (finiteTarget_two_basis Q hQ)
      (fun i ↦ f (FreeGroup.of i)) continuous_of_discreteTopology i
  refine ⟨ψ, ?_⟩
  have he : (fun r ↦ ψ (completionMap x r)) = fun r ↦ completedFiniteMap Q f r := by
    apply (ProfiniteGrp.ProfiniteCompletion.denseRange
      (G := GrpCat.of (FreeGroup ι))).equalizer
      (ψ.continuous_toFun.comp (completionMap x).continuous_toFun)
      (completedFiniteMap Q f).hom.continuous_toFun
    funext w
    change ψ (completionMap x (wordCompletion ι w)) =
      completedFiniteMap Q f (wordCompletion ι w)
    rw [completionMap_word, completedFiniteMap_word]
    exact DFunLike.congr_fun hword w
  intro r
  exact congrFun he r

/-- Closed normal consequence in the actual free pro-two group implies
the existing literal finite-test predicate used by completed Fox theory. -/
theorem completedProTwoConsequence_of_normalClosure
    [Fintype ι] (x : ι → G)
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (relations : Set (CompletedWords ι)) (r : CompletedWords ι)
    (hr : completionMap x r ∈ closedNormalClosure (completionMap x '' relations)) :
    CompletedProTwoConsequence relations r := by
  intro N _ _ hN hrel
  obtain ⟨ψ, hψ⟩ := exists_finite_evaluation_factor x hfree
    (FreeGroup ι ⧸ N) hN (QuotientGroup.mk' N)
  have hle : closedNormalClosure (completionMap x '' relations) ≤ ψ.toMonoidHom.ker := by
    apply closedNormalClosure_le_closed_normal
      (ProCGroups.ContinuousMonoidHom.isClosed_ker ψ)
    rintro _ ⟨s, hs, rfl⟩
    change ψ (completionMap x s) = 1
    rw [hψ]
    exact hrel s hs
  have hzero : ψ (completionMap x r) = 1 := hle hr
  rw [hψ] at hzero
  exact hzero

/-- Actual continuous maps commute with completed finite evaluation. -/
theorem finiteMap_comp_completionMap (x : ι → G)
    (Q : Type) [Group Q] [Finite Q]
    (π : G →ₜ* ProfiniteGrp.ofFiniteGrp (FiniteGrp.of Q)) (r : CompletedWords ι) :
    π (completionMap x r) =
      completedFiniteMap Q (π.toMonoidHom.comp (FreeGroup.lift x)) r := by
  have he : (fun r ↦ π (completionMap x r)) = fun r ↦
      completedFiniteMap Q (π.toMonoidHom.comp (FreeGroup.lift x)) r := by
    apply (ProfiniteGrp.ProfiniteCompletion.denseRange
      (G := GrpCat.of (FreeGroup ι))).equalizer
      (π.continuous_toFun.comp (completionMap x).continuous_toFun)
      (completedFiniteMap Q (π.toMonoidHom.comp (FreeGroup.lift x))).hom.continuous_toFun
    funext w
    change π (completionMap x (wordCompletion ι w)) =
      completedFiniteMap Q (π.toMonoidHom.comp (FreeGroup.lift x)) (wordCompletion ι w)
    rw [completionMap_word, completedFiniteMap_word]
    rfl
  exact congrFun he r

/-- The right component of the finite affine Fox evaluation is the actual
ordinary finite evaluation on every completed word. -/
theorem completedWordEvaluation_eq_finiteMap [Fintype ι]
    (Q : Type) [Group Q] [Finite Q] (y : ι → Q) (r : CompletedWords ι) :
    completedWordEvaluation Q y r = completedFiniteMap Q (FreeGroup.lift y) r := by
  obtain ⟨w, hw, hq⟩ := exists_word_matching_pair
    (FoxAffine (ZMod 2) Q (ι := ι)) Q
    (foxLift (ZMod 2) Q y) (FreeGroup.lift y) r
  have he := congrArg (fun a : FoxAffine (ZMod 2) Q (ι := ι) ↦ a.right) hw
  change (foxLift (ZMod 2) Q y w).right = completedWordEvaluation Q y r at he
  rw [foxLift_right] at he
  exact he.symm.trans hq

private theorem lift_comp_generators (x : ι → G)
    (Q : Type) [Group Q] (π : G →* Q) :
    FreeGroup.lift (fun i ↦ π (x i)) = π.comp (FreeGroup.lift x) := by
  apply FreeGroup.lift.symm.injective
  funext i
  change FreeGroup.lift (fun j ↦ π (x j)) (FreeGroup.of i) = π (FreeGroup.lift x (FreeGroup.of i))
  simp only [FreeGroup.lift_apply_of]

/-- A genuine closed-kernel presentation of a finite quotient of an actual
free pro-two source supplies the literal completed Fox presentation test. -/
theorem completedProTwoPresentation_of_closed_kernel [Fintype ι]
    (x : ι → G) (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (Q : Type) [Group Q] [Finite Q]
    (π : G →ₜ* ProfiniteGrp.ofFiniteGrp (FiniteGrp.of Q))
    (relations : Set (CompletedWords ι))
    (hkernel : π.toMonoidHom.ker = closedNormalClosure (completionMap x '' relations)) :
    CompletedProTwoPresentation Q (fun i ↦ π (x i)) relations := by
  constructor
  · intro r hr
    rw [completedWordEvaluation_eq_finiteMap]
    erw [lift_comp_generators x Q π.toMonoidHom,
      ← finiteMap_comp_completionMap]
    change completionMap x r ∈ π.toMonoidHom.ker
    rw [hkernel]
    exact subset_closedNormalClosure _ ⟨r, hr, rfl⟩
  · intro N _ _ hN hrel
    obtain ⟨ψ, hψ⟩ := exists_finite_evaluation_factor x hfree
      (FreeGroup ι ⧸ N) hN (QuotientGroup.mk' N)
    have hle : closedNormalClosure (completionMap x '' relations) ≤ ψ.toMonoidHom.ker := by
      apply closedNormalClosure_le_closed_normal
        (ProCGroups.ContinuousMonoidHom.isClosed_ker ψ)
      rintro _ ⟨s, hs, rfl⟩
      change ψ (completionMap x s) = 1
      rw [hψ]
      exact hrel s hs
    intro w hw
    have hwπ : FreeGroup.lift x w ∈ π.toMonoidHom.ker := by
      change π (FreeGroup.lift x w) = 1
      change FreeGroup.lift (fun i ↦ π (x i)) w = 1 at hw
      erw [lift_comp_generators x Q π.toMonoidHom] at hw
      exact hw
    rw [hkernel] at hwπ
    have hz : ψ (FreeGroup.lift x w) = 1 := hle hwπ
    have he := hψ (wordCompletion ι w)
    rw [completionMap_word, completedFiniteMap_word] at he
    exact (QuotientGroup.eq_one_iff w).mp (he.symm.trans hz)

/-- Closed normal consequences in an actual free pro-two group give rows
in the actual completed Fox relation module of any finite two-group quotient. -/
theorem completedFoxDerivative_mem_of_proTwo_normalClosure [Fintype ι]
    (x : ι → G) (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (Q : Type) [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) (y : ι → Q)
    (relations : Set (CompletedWords ι))
    (hrel : ∀ s ∈ relations, completedWordEvaluation Q y s = 1)
    (r : CompletedWords ι)
    (hr : completionMap x r ∈ closedNormalClosure (completionMap x '' relations)) :
    completedFoxDerivative Q y r ∈ completedFoxRelationModule Q y relations :=
  completedFoxDerivative_mem_of_proTwoConsequence Q y hQ relations hrel r
    (completedProTwoConsequence_of_normalClosure x hfree relations r hr)

end UnitDistance.GroupAugmentation
