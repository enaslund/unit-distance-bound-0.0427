/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import Mathlib.Topology.Algebra.ClopenNhdofOne

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Open-normal neighborhood bases at the identity

Every identity neighborhood in a profinite group contains an open normal subgroup. This file
packages that refinement result for later basis, separation, and inverse-limit arguments.
-/

namespace ProCGroups.ProC

universe u v

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
In a compact totally disconnected topological group, any open neighborhood of \(1\) contains an
open normal subgroup.
-/
theorem exists_openNormalSubgroup_sub_open_nhds_of_one [CompactSpace G]
    [TotallyDisconnectedSpace G] {W : Set G} (hW : IsOpen W) (h1W : (1 : G) ∈ W) :
    ∃ U : OpenNormalSubgroup G, ((U : Subgroup G) : Set G) ⊆ W := by
  obtain ⟨U, hU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1W
  exact ⟨U, fun _ hx ↦ hU hx⟩

end

end ProCGroups.ProC
