module

public import UnitDistance.DyadicGroup
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! Canonical discrete topology on the finite dyadic group. -/
namespace UnitDistance.Dyadic.D
instance topology : TopologicalSpace Dyadic.D := ⊥
instance discrete : DiscreteTopology Dyadic.D := ⟨rfl⟩
instance topologicalGroup : IsTopologicalGroup Dyadic.D := inferInstance
instance t2 : T2Space Dyadic.D := inferInstance
end UnitDistance.Dyadic.D
