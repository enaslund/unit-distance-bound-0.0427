module

public import UnitDistance.SigmaOriginalRelators
public import UnitDistance.OriginalRelatorGeneration
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.PresentationQuotientEquiv

@[expose] public section
set_option backward.privateInPublic true


/-! The proved arithmetic relators generate the actual relation kernel once
the sharp cohomological bound on the actual maximal arithmetic group is
supplied. This is a conditional interface, not an arithmetic H² bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.Cohomology ProCGroups.Presentations

/-- No independent word, detector, or normal-generation premise remains. -/
theorem sigmaOriginalRelator_generates_of_h2_bound
    [FiniteDimensional (ZMod 2) (continuousCohomologyZModPLifted 2 SigmaGroup 2)]
    (hbound : Module.finrank (ZMod 2)
      (continuousCohomologyZModPLifted 2 SigmaGroup 2)≤6) :
    closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : SigmaFree)))=
      (sigmaRelationKernel : Subgroup SigmaFree) := by
  let e := continuousCohomologyZModPLiftedLinearEquiv (p := 2) sigmaFreeQuotientEquiv 2
  letI : FiniteDimensional (ZMod 2)
      (continuousCohomologyZModPLifted 2 (SigmaFree ⧸ (sigmaRelationKernel : Subgroup SigmaFree)) 2) :=
    e.finiteDimensional
  apply OriginalRelatorGeneration.closedNormalClosure_eq_of_original_images
    (FiniteFreeProTwo.isFree 7).hasOpenNormalBasisInClass sigmaRelationKernel
    sigmaFreeMap_minimal sigmaOriginalRelator sigmaUniversalDetector sigmaOriginalRelator_quadratic
  rw [← e.finrank_eq]
  exact hbound

end UnitDistance.ArithmeticProP
