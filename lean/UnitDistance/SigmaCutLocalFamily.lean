module

public import UnitDistance.SigmaCutOdd
public import UnitDistance.SigmaCutCyclic
public import UnitDistance.ArithmeticLocalBlockCosts
public import UnitDistance.SigmaDyadicCompletedRelation
public import UnitDistance.ProTwoCompletedLocalFamily
public import UnitDistance.FilteredCompletedBlockPresentation

@[expose] public section
set_option backward.privateInPublic true


/-! The actual local block family of the twenty-seven-word arithmetic cut. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace UnitDistance.ArithmeticProP.SigmaCut
open GroupAugmentation ProCGroups ProCGroups.Presentations ArithmeticLocalBlocks

abbrev actualExtra := ExtraPrime.freeFrobenius
abbrev ActualQuotient := Quotient actualExtra

def otherSource : ∀j : Index,GeneratorType j → Source
  | none => fun _=>sigmaFreeConjugation
  | some (.inl i) => ![sigmaFreeOddInertia i,sigmaFreeOddFrobenius i]
  | some (.inr i) => fun _=>actualExtra i

def otherMap : ∀j : Index,LocalGroup j →* ActualQuotient
  | none => infinityMap actualExtra
  | some (.inl i) => oddMap actualExtra i
  | some (.inr i) => extraMap actualExtra i

theorem otherMap_generator (j : Index) (i : GeneratorType j) :
    otherMap j (ArithmeticLocalBlocks.generators j i)=projection actualExtra (otherSource j i) := by
  cases j with
  | none => exact OddLocal.cyclicMap_generator 2 (infinityElement actualExtra) (infinity_square actualExtra)
  | some j =>
    cases j with
    | inl j =>
      fin_cases i
      · exact oddMap_inertia actualExtra j
      · exact oddMap_frobenius actualExtra j
    | inr j => exact OddLocal.cyclicMap_generator 4 (extraElement actualExtra j) (extra_fourth actualExtra j)

theorem otherMap_layers (j : Index) (n : ℕ) :
    Function.Injective (layerMap (ZMod 2) (LocalGroup j) (otherMap j) n) := by
  cases j with
  | none => exact infinityMap_layers actualExtra n
  | some j =>
    cases j with
    | inl j => exact oddMap_layers actualExtra j n
    | inr j => exact extraMap_layers j n

def otherLifts (j : Index) (i : GeneratorType j) : CompletedWords (Fin 7) :=
  SigmaDyadic.completedLift 7 (otherSource j i)

abbrev AllIndex := Option Index
abbrev AllGeneratorType := withDyadicIndices GeneratorType

def allGroup : AllIndex → Type
  | none => Dyadic.D
  | some j => LocalGroup j
instance allGroup_group (j : AllIndex) : Group (allGroup j) := by
  cases j <;> dsimp [allGroup] <;> infer_instance
instance allGroup_finite (j : AllIndex) : Finite (allGroup j) := by
  cases j <;> dsimp [allGroup] <;> infer_instance

def allGenerators : ∀j : AllIndex,AllGeneratorType j → allGroup j
  | none => Dyadic.Filtration.gen
  | some j => ArithmeticLocalBlocks.generators j

def allSource : ∀j : AllIndex,AllGeneratorType j → Source
  | none => SigmaDyadic.globalXYZ
  | some j => otherSource j

def allLifts : ∀j : AllIndex,AllGeneratorType j → CompletedWords (Fin 7)
  | none => SigmaDyadic.completedGlobalXYZ
  | some j => otherLifts j

theorem allLifts_map (j : AllIndex) (i : AllGeneratorType j) :
    completionMap (FiniteFreeProTwo.generator 7) (allLifts j i)=allSource j i := by
  cases j
  · exact SigmaDyadic.completedGlobalXYZ_map i
  · exact SigmaDyadic.completedLift_map 7 _

def allRelations : Set (CompletedWords (Fin 7)) :=
  completedGeneratorRelationFamily AllGeneratorType allLifts
    (completeLocalRelations AllGeneratorType allGroup allGenerators)

/-- The genuine dyadic initial is evaluated in the exact same completed
local generator lifts used by the global relation family. -/
theorem allLifts_dyadic_relation :
    completedGeneratorSubstitution (allLifts none) SigmaDyadic.completedRelation=
      SigmaDyadic.completedGlobalRelation := rfl

end UnitDistance.ArithmeticProP.SigmaCut

namespace UnitDistance.ArithmeticProP.SigmaCut
open GroupAugmentation ProCGroups ProCGroups.Presentations ArithmeticLocalBlocks

abbrev ArithmeticPresentation : Prop :=
  closedNormalClosure (Set.range (fun i↦(sigmaOriginalRelator i : Source)))=
    (sigmaRelationKernel : Subgroup Source)

def actualDyadicMap
    (hgen : closedNormalClosure (Set.range (fun i↦(sigmaOriginalRelator i : Source)))=
      (sigmaRelationKernel : Subgroup Source)) : Dyadic.D →ₜ* ActualQuotient :=
  Classical.choose (dyadic_map actualExtra hgen)

theorem actualDyadicMap_properties (hgen : ArithmeticPresentation) :
    Function.Injective (actualDyadicMap hgen) ∧
      (actualDyadicMap hgen).comp Dyadic.ArithmeticPresentation.model=
        (projection actualExtra).comp SigmaDyadic.toSigmaFree ∧
      (retained actualExtra).toMonoidHom.comp (actualDyadicMap hgen).toMonoidHom=
        SigmaDyadic.retainedDyadic := Classical.choose_spec (dyadic_map actualExtra hgen)

theorem actualDyadicMap_generator (hgen : ArithmeticPresentation) (i : Fin 3) :
    actualDyadicMap hgen (Dyadic.Filtration.gen i)=projection actualExtra (SigmaDyadic.globalXYZ i) := by
  have h := congrArg (fun f : SigmaDyadic.LocalSource →ₜ* ActualQuotient=>f (SigmaDyadic.localXYZ i))
    (actualDyadicMap_properties hgen).2.1
  change actualDyadicMap hgen (Dyadic.ArithmeticPresentation.model (SigmaDyadic.localXYZ i))=_ at h
  have he : Dyadic.ArithmeticPresentation.model (SigmaDyadic.localXYZ i)=Dyadic.Filtration.gen i := by
    fin_cases i <;> simp [SigmaDyadic.localXYZ,Dyadic.Filtration.gen]
  rw [he] at h
  exact h

def allMap (hgen : ArithmeticPresentation) : ∀j : AllIndex,allGroup j →* ActualQuotient
  | none => (actualDyadicMap hgen).toMonoidHom
  | some j => otherMap j

theorem allMap_generator (hgen : ArithmeticPresentation) (j : AllIndex) (i : AllGeneratorType j) :
    allMap hgen j (allGenerators j i)=projection actualExtra (allSource j i) := by
  cases j
  · exact actualDyadicMap_generator hgen i
  · exact otherMap_generator _ i

/-- Undo only the harmless central shifts of the three actual local lifts. -/
def canonicalRetained : ActualQuotient →* RetainedQuadratic.Q :=
  (ClassTwo.GroupModel.centralShear RetainedQuadratic.cocycle
    (RetainedQuadratic.dyadicAdjustment
      (SigmaDyadic.retainedLocal Dyadic.ArithmeticPresentation.x).central
      (SigmaDyadic.retainedLocal Dyadic.ArithmeticPresentation.y).central
      (SigmaDyadic.retainedLocal Dyadic.ArithmeticPresentation.z).central)).symm.toMonoidHom.comp
        (retained actualExtra).toMonoidHom

theorem canonicalRetained_diagram (hgen : ArithmeticPresentation) :
    canonicalRetained.comp (actualDyadicMap hgen).toMonoidHom=RetainedQuadratic.dyadicMap := by
  apply MonoidHom.ext
  intro d
  have h := DFunLike.congr_fun (actualDyadicMap_properties hgen).2.2 d
  change retained actualExtra (actualDyadicMap hgen d)=SigmaDyadic.retainedDyadic d at h
  change (ClassTwo.GroupModel.centralShear RetainedQuadratic.cocycle _).symm
    (retained actualExtra (actualDyadicMap hgen d))=RetainedQuadratic.dyadicMap d
  rw [h]
  exact (ClassTwo.GroupModel.centralShear RetainedQuadratic.cocycle _).symm_apply_apply _

end UnitDistance.ArithmeticProP.SigmaCut
