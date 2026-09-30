module

public import UnitDistance.GeometryProjection

@[expose] public section
set_option backward.privateInPublic true


/-!
# Constructing the finite window without enumeration assumptions

A closed discrete additive subgroup meets each translated compact window
in finitely many points. This supplies a canonical finite set for the
membership hypotheses of the geometric transfer theorems.
-/

open scoped Classical

namespace UnitDistance

/-- Compact-window finiteness uses the full ambient topology and a closed
discrete lattice, including products with nonarchimedean factors. -/
theorem finite_lattice_window {X : Type*} [AddGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (L : AddSubgroup X) [DiscreteTopology L]
    (hL : IsClosed (L : Set X)) (Ω : Set X) (hΩ : IsCompact Ω) (h : X) :
    {l : L | (l : X) + h ∈ Ω}.Finite := by
  apply isCompact_iff_finite.mp
  exact ((Homeomorph.addRight h).isClosedEmbedding.comp hL.isClosedEmbedding_subtypeVal).isCompact_preimage hΩ

/-- The genuine lattice points in a translated compact window. -/
noncomputable def compactLatticeWindow {X : Type*} [AddGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (L : AddSubgroup X) [DiscreteTopology L]
    (hL : IsClosed (L : Set X)) (Ω : Set X) (hΩ : IsCompact Ω) (h : X) : Finset L :=
  (finite_lattice_window L hL Ω hΩ h).toFinset

@[simp] theorem mem_compactLatticeWindow {X : Type*} [AddGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (L : AddSubgroup X) [DiscreteTopology L]
    (hL : IsClosed (L : Set X)) (Ω : Set X) (hΩ : IsCompact Ω) (h : X) (l : L) :
    l ∈ compactLatticeWindow L hL Ω hΩ h ↔ (l : X) + h ∈ Ω :=
  Set.Finite.mem_toFinset _

/-- A subset of a compact window is finite as well; the actual window
need not be closed and no boundary-measure assumption is used. -/
theorem finite_lattice_window_of_subset {X : Type*} [AddGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (L : AddSubgroup X) [DiscreteTopology L]
    (hL : IsClosed (L : Set X)) (Ω K : Set X) (hK : IsCompact K)
    (hΩK : Ω ⊆ K) (h : X) : {l : L | (l : X) + h ∈ Ω}.Finite :=
  (finite_lattice_window L hL K hK h).subset (fun _ hl => hΩK hl)

end UnitDistance
