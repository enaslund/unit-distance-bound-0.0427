module

public import UnitDistance.GroupAugmentationRetainedQuadratic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Instances.Discrete

@[expose] public section
set_option backward.privateInPublic true


/-! The canonical discrete profinite topology on the actual finite retained model. -/
namespace UnitDistance.RetainedQuadratic

instance retainedTopology : TopologicalSpace Q := ⊥
instance retainedDiscrete : DiscreteTopology Q := ⟨rfl⟩
instance retainedTopologicalGroup : IsTopologicalGroup Q := inferInstance
instance retainedT2 : T2Space Q := inferInstance
instance retainedCompact : CompactSpace Q := inferInstance
instance retainedTotallyDisconnected : TotallyDisconnectedSpace Q := inferInstance

end UnitDistance.RetainedQuadratic
