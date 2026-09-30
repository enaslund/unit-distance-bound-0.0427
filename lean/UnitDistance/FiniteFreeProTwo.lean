module

public import UnitDistance.Upstream.Yamaguchi.ProCGroups.FreeProC.Construction
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProP.MinimalEpimorphism

@[expose] public section
set_option backward.privateInPublic true


/-!
# A constructed finite-rank free pro-two source

The actual pro-two completion has the full lifting property into arbitrary
pro-two targets. The proof follows the completion lifting argument in the
attributed public FreeProC.Basic source, without its unnecessary generating
image premise. This supplies the stronger interface used by completed Fox.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.FiniteFreeProTwo
open ProCGroups ProCGroups.ProC ProCGroups.FreeProC ClassFieldTower.ProP
open ProCGroups.Generation ProCGroups.FiniteGeneration

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance freeGroupTopology (d : ℕ) : TopologicalSpace (FreeGroup (Fin d)) := ⊥
local instance freeGroupDiscrete (d : ℕ) : DiscreteTopology (FreeGroup (Fin d)) := ⟨rfl⟩

def source (d : ℕ) : EpimorphicallyFreeProCGroupOnConvergingSetData (FiniteGroupClass.pGroup 2) :=
  finiteFreeProCSource (FiniteGroupClass.pGroup 2) (FiniteGroupClass.pGroup_formation 2)
    (FiniteGroupClass.pGroup_hereditary 2) (Fin d)

abbrev Carrier (d : ℕ) := (source d).carrier

def generator (d : ℕ) (i : Fin d) : Carrier d := (source d).inclusion i

/-- The constructed finite-rank source satisfies the full free pro-two
universal property, including maps whose image does not generate the target. -/
theorem isFree (d : ℕ) : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) (generator d) := by
  let ι := Completion.proCCompletionMap (FiniteGroupClass.pGroup 2)
    (FiniteGroupClass.pGroup_formation 2) (FreeGroup (Fin d))
  have hι := Completion.proCCompletion_isProCCompletion (FiniteGroupClass.pGroup 2)
    (FiniteGroupClass.pGroup_formation 2) (FiniteGroupClass.pGroup_hereditary 2)
    (FreeGroup (Fin d))
  have hep := proCCompletionOfAbstractFreeGroup_is_free hι
  change IsFreeProCGroup (C := FiniteGroupClass.pGroup 2)
    (fun i : Fin d ↦ ι (FreeGroup.of i))
  refine ⟨hι.hasOpenNormalBasisInClass, continuous_of_discreteTopology, hep.generates_range, ?_⟩
  intro G _ _ _ _ _ _ hG φ _hφ
  let φfree : FreeGroup (Fin d) →ₜ* G :=
    { toMonoidHom := FreeGroup.lift φ
      continuous_toFun := continuous_of_discreteTopology }
  let φhat := hι.lift hG φfree
  refine ⟨φhat.toMonoidHom, ?_, ?_⟩
  · refine ⟨φhat.continuous_toFun, ?_⟩
    intro x
    have hfac := congrArg (fun ψ : FreeGroup (Fin d) →ₜ* G ↦ ψ (FreeGroup.of x))
      (hι.lift_spec hG φfree)
    exact hfac.trans (by
      change FreeGroup.lift φ (FreeGroup.of x) = φ x
      exact FreeGroup.lift_apply_of)
  · intro g hg
    let gCont : Carrier d →ₜ* G := ⟨g, hg.1⟩
    have hfac : gCont.comp ι = φfree := by
      apply ContinuousMonoidHom.toMonoidHom_injective
      ext x
      change g (ι (FreeGroup.of x)) = FreeGroup.lift φ (FreeGroup.of x)
      exact (hg.2 x).trans (by simp only [FreeGroup.lift_apply_of])
    exact congrArg ContinuousMonoidHom.toMonoidHom (hι.lift_unique hG φfree hfac)

/-- The constructed source has exactly the specified generator rank. -/
theorem generatorRank (d : ℕ) : topologicalGeneratorRank (Carrier d) = d := by
  have hcyc : ∃ (A : Type) (_ : Group A) (_ : Finite A),
      FiniteGroupClass.pGroup 2 A ∧ IsCyclic A ∧ Nontrivial A := by
    refine ⟨Multiplicative (ZMod 2), inferInstance, inferInstance,
      ⟨inferInstance, ?_⟩, inferInstance, inferInstance⟩
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
    simp
  letI : Finite (source d).basis := by
    change Finite (Fin d)
    infer_instance
  have h := basisCard_eq_topologicalRank_of_finiteBasis (FiniteGroupClass.pGroup 2)
    (FiniteGroupClass.pGroup_formation 2).quotientClosed hcyc (source d)
  have hd : topologicalRank (Carrier d) = (d : Cardinal) := by
    rw [← h]
    change Cardinal.mk (Fin d) = (d : Cardinal)
    simp
  unfold topologicalGeneratorRank
  rw [hd]
  simp

/-- Specified actual generators of a pro-two group lift to a surjection
from the constructed source. Equality of ranks proves the kernel is Frattini. -/
theorem exists_minimal_surjection_for_generators
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasPGroupOpenNormalBasis 2 G) (d : ℕ) (x : Fin d → G)
    (hgen : TopologicallyGenerates (Set.range x)) (hrank : topologicalGeneratorRank G = d) :
    ∃ π : Carrier d →ₜ* G, Function.Surjective π ∧
      π.toMonoidHom.ker ≤ closedPowerCommutator 2 (Carrier d) ∧
      ∀ i, π (generator d i) = x i := by
  classical
  let π := (isFree d).liftHom hG x continuous_of_discreteTopology
  have hπ (i : Fin d) : π (generator d i) = x i :=
    (isFree d).liftHom_apply hG x continuous_of_discreteTopology i
  have hsurj : Function.Surjective π := by
    apply surjective_hom_of_rangeContainsGeneratingSet hgen π.continuous_toFun
    rintro _ ⟨i, rfl⟩
    exact ⟨generator d i, hπ i⟩
  have hsource : TopologicallyFinitelyGenerated (Carrier d) := by
    refine ⟨Finset.univ.image (generator d), ?_⟩
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using (isFree d).generates_range
  have htarget : TopologicallyFinitelyGenerated G := by
    refine ⟨Finset.univ.image x, ?_⟩
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hgen
  refine ⟨π, hsurj, ?_, hπ⟩
  exact ker_le_closedPowerCommutator_of_generatorRank_eq 2
    (isFree d).hasOpenNormalBasisInClass hG hsource htarget π hsurj
    ((generatorRank d).trans hrank.symm)

end UnitDistance.FiniteFreeProTwo
