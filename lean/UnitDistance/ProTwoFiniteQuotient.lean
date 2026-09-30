module

public import UnitDistance.ProTwoCompletedConsequence
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProC.OpenNormalSubgroups.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! Finite continuous images of actual free pro-two groups are actual
finite two-groups with the displayed generators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.GroupAugmentation
open ProCGroups ProCGroups.ProC ProCGroups.FreeProC
variable {ι G P : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [DiscreteTopology P]
  [TopologicalSpace ι] [DiscreteTopology ι]

theorem isPGroup_of_freeProTwo_surjective (x : ι → G)
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (π : G →ₜ* P) (hπ : Function.Surjective π) : IsPGroup 2 P := by
  have h := HasOpenNormalBasisInClass.quotient_mem
    (FiniteGroupClass.pGroup_formation 2) hfree.hasOpenNormalBasisInClass
    (OpenNormalSubgroup.ker π)
  exact h.2.of_equiv (QuotientGroup.quotientKerEquivOfSurjective π.toMonoidHom hπ)

theorem generates_of_freeProTwo_surjective (x : ι → G)
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (π : G →ₜ* P) (hπ : Function.Surjective π) :
    Subgroup.closure (Set.range (fun i=>π (x i)))=⊤ :=
  (FiniteGeneration.topologicallyGenerates_iff_subgroupClosure_eq_top_of_discrete).mp
    (FiniteGeneration.topologicallyGenerates_range_comp_of_surjective π hπ x hfree.generates_range)

end UnitDistance.GroupAugmentation
