module

public import UnitDistance.PadicTwoGlobalGenus
public import UnitDistance.SigmaFreeRetained

@[expose] public section
set_option backward.privateInPublic true


/-! The actual local presentation lifts into the actual free arithmetic
source, with a commuting square, literal retained coordinates, and a genuine
global kernel element carrying the proved local quadratic relation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace UnitDistance.SigmaDyadic
open ProCGroups ProCGroups.ProC ArithmeticProP ClassFieldTower.ProP
abbrev LocalSource := PadicTwoQuadraticRelation.Source
abbrev GlobalSource := FiniteFreeProTwo.Carrier 7

def localPresentation : LocalSource →ₜ* PadicTwoMaximalProTwo.Group :=
  Classical.choose PadicTwoQuadraticRelation.exists_actual_quadratic_relation

theorem localPresentation_surjective : Function.Surjective localPresentation :=
  (Classical.choose_spec PadicTwoQuadraticRelation.exists_actual_quadratic_relation).1

theorem localPresentation_minimal :
    localPresentation.toMonoidHom.ker ≤ closedPowerCommutator 2 LocalSource :=
  (Classical.choose_spec PadicTwoQuadraticRelation.exists_actual_quadratic_relation).2.1

theorem localPresentation_generator (i : Fin 3) :
    localPresentation (FiniteFreeProTwo.generator 3 i)=PadicTwoQuadraticRelation.generator i :=
  (Classical.choose_spec PadicTwoQuadraticRelation.exists_actual_quadratic_relation).2.2.1 i

def genuineRelation : LocalSource :=
  Classical.choose (Classical.choose_spec PadicTwoQuadraticRelation.exists_actual_quadratic_relation).2.2.2

theorem genuineRelation_killed : localPresentation genuineRelation=1 :=
  (Classical.choose_spec (Classical.choose_spec
    PadicTwoQuadraticRelation.exists_actual_quadratic_relation).2.2.2).1

theorem genuineRelation_detector : PadicTwoQuadraticRelation.detector genuineRelation=
    FreeThreeQuadratic.relation :=
  (Classical.choose_spec (Classical.choose_spec
    PadicTwoQuadraticRelation.exists_actual_quadratic_relation).2.2.2).2

/-- Actual free-source preimages of the local arithmetic generators. -/
def liftGenerator (i : Fin 3) : GlobalSource :=
  Function.surjInv sigmaFreeMap_surjective
    (PadicTwoGlobalMap.toGlobal (PadicTwoQuadraticRelation.generator i))

theorem liftGenerator_image (i : Fin 3) : sigmaFreeMap (liftGenerator i)=
    PadicTwoGlobalMap.toGlobal (PadicTwoQuadraticRelation.generator i) :=
  Function.surjInv_eq sigmaFreeMap_surjective _

def toSigmaFree : LocalSource →ₜ* GlobalSource :=
  (FiniteFreeProTwo.isFree 3).liftHom (FiniteFreeProTwo.isFree 7).hasOpenNormalBasisInClass
    liftGenerator continuous_of_discreteTopology

theorem toSigmaFree_generator (i : Fin 3) : toSigmaFree (FiniteFreeProTwo.generator 3 i)=liftGenerator i :=
  (FiniteFreeProTwo.isFree 3).liftHom_apply (FiniteFreeProTwo.isFree 7).hasOpenNormalBasisInClass
    liftGenerator continuous_of_discreteTopology i

/-- The map of free sources agrees exactly with the actual arithmetic maps. -/
theorem commuting_square : sigmaFreeMap.comp toSigmaFree=
    PadicTwoGlobalMap.toGlobal.comp localPresentation := by
  apply ContinuousMonoidHom.toMonoidHom_injective
  apply (FiniteFreeProTwo.isFree 3).hom_ext maximalSigmaProTwo_hasPGroupOpenNormalBasis
    (sigmaFreeMap.comp toSigmaFree).continuous
    (PadicTwoGlobalMap.toGlobal.comp localPresentation).continuous
  intro i
  change sigmaFreeMap (toSigmaFree (FiniteFreeProTwo.generator 3 i))=
    PadicTwoGlobalMap.toGlobal (localPresentation (FiniteFreeProTwo.generator 3 i))
  rw [toSigmaFree_generator,liftGenerator_image,localPresentation_generator]

theorem commuting_square_apply (r : LocalSource) : sigmaFreeMap (toSigmaFree r)=
    PadicTwoGlobalMap.toGlobal (localPresentation r) :=
  congrArg (fun f : LocalSource →ₜ* Gal(maximalSigmaProTwo/ℚ) => f r) commuting_square

/-- The genuine local relation is an actual global relation after lifting. -/
theorem genuineRelation_mem_global_kernel : toSigmaFree genuineRelation∈sigmaRelationKernel := by
  change sigmaFreeMap (toSigmaFree genuineRelation)=1
  rw [commuting_square_apply,genuineRelation_killed,map_one]

/-- Consequently its image in the independently constructed retained field is trivial. -/
theorem genuineRelation_retained : sigmaFreeRetainedMap (toSigmaFree genuineRelation)=1 := by
  change sigmaRetainedModelMap (sigmaFreeMap (toSigmaFree genuineRelation))=1
  rw [commuting_square_apply,genuineRelation_killed,map_one,map_one]

theorem liftGenerator_base (i : Fin 3) : (sigmaFreeRetainedMap (liftGenerator i)).base=
    RetainedQuadratic.binaryVector 7 (![53,2,108] i) := by
  change (sigmaRetainedModelMap (sigmaFreeMap (liftGenerator i))).base=_
  rw [liftGenerator_image,sigmaRetainedModelMap_base,PadicTwoGlobalMap.localGenerator_genus]

/-- The three retained local generators x=b, y=a, z=a*c in the actual free
arithmetic source have the required masks 2,53,89. -/
theorem retained_basis_base :
    (sigmaFreeRetainedMap (liftGenerator 1)).base=RetainedQuadratic.binaryVector 7 2 ∧
    (sigmaFreeRetainedMap (liftGenerator 0)).base=RetainedQuadratic.binaryVector 7 53 ∧
    (sigmaFreeRetainedMap (liftGenerator 0*liftGenerator 2)).base=RetainedQuadratic.binaryVector 7 89 := by
  refine ⟨liftGenerator_base 1,liftGenerator_base 0,?_⟩
  rw [map_mul,ClassTwo.GroupModel.mul_base,liftGenerator_base,liftGenerator_base]
  have h : RetainedQuadratic.binaryVector 7 53+RetainedQuadratic.binaryVector 7 108=
      RetainedQuadratic.binaryVector 7 89 := by decide +kernel
  exact h

end UnitDistance.SigmaDyadic
