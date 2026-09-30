/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# LubinTate the explicit norm-subgroup computation: the standard level lies in the higher-unit fixed field
-/

noncomputable section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

noncomputable local instance equalCharacteristicHigherUnitMembershipBaseAlgebra
    (F : LocalField K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedFrobeniusFixedBaseAlgebra F

noncomputable local instance equalCharacteristicHigherUnitMembershipLevelAlgebra
    (F : LocalField K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedFrobeniusFixedLevelAlgebra F n

local instance equalCharacteristicHigherUnitMembershipScalarTower
    (F : LocalField K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- States the theorem `equalCharacteristicLubinTateLevelFieldToCompleted_mem_fixedField_of_mem_higherUnit`. -/
theorem
    equalCharacteristicLubinTateLevelFieldToCompleted_mem_fixedField_of_mem_higherUnit
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n)
    (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicLubinTateLevelFieldToCompleted F n x ∈
      equalCharacteristicCompletedFrobeniusFixedField F a n := by
  rw [equalCharacteristicCompletedFrobeniusFixedField,
    IntermediateField.mem_fixedField_iff]
  intro sigma hsigma
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hsigma
  have hfixed :
      equalCharacteristicLubinTateLevelFieldToCompleted F n x ∈
        MulAction.fixedBy (equalCharacteristicCompletedLevelField F n)
          (equalCharacteristicCompletedFrobeniusAlgEquiv F a n) := by
    rw [MulAction.mem_fixedBy]
    exact
      equalCharacteristicCompletedFrobeniusAlgEquiv_comp_levelFieldToCompleted_of_mem_higherUnit
        F a n ha x
  exact MulAction.mem_fixedBy_zpow hfixed j

end EqualCharacteristic
end LubinTate
