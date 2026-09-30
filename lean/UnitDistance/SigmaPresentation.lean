module

public import UnitDistance.SigmaRelatorGeneration
public import UnitDistance.MaximalSigmaH2Bound

@[expose] public section
set_option backward.privateInPublic true


/-! The six actual arithmetic relators present the actual maximal rational
pro-two extension unramified outside 2,3,5,7,11,13. -/
noncomputable section
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.Cohomology ProCGroups.Presentations

/-- The six proved original arithmetic words generate the actual relation kernel. -/
theorem sigmaOriginalRelator_generates :
    closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : SigmaFree))) =
      (sigmaRelationKernel : Subgroup SigmaFree) := by
  obtain ⟨hfinite,hbound⟩ := maximalSigmaProTwoH2_finiteDimensional_finrank_le
  letI : FiniteDimensional (ZMod 2) (continuousCohomologyZModPLifted 2 SigmaGroup 2) := hfinite
  exact sigmaOriginalRelator_generates_of_h2_bound hbound

end UnitDistance.ArithmeticProP
