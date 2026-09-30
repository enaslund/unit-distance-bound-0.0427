/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# LubinTate the explicit norm-subgroup computation: the standard level is the higher-unit fixed field

The standard-level embedding is an equivalence because its source and target
have the same degree `(q - 1) q^n`.
-/

noncomputable section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

attribute [local instance]
  equalCharacteristicCompletedFrobeniusFixedBaseAlgebra
  equalCharacteristicLubinTateLevelFieldAlgebra
  equalCharacteristicLubinTateLevelFieldSMul
  equalCharacteristicLubinTateLevelFieldModule
  equalCharacteristicCompletedFrobeniusFixedFieldAlgebra
  equalCharacteristicCompletedFrobeniusFixedFieldSMul
  equalCharacteristicCompletedFrobeniusFixedFieldModule

/-- Defines `equalCharacteristicLubinTateLevelFieldEquivFixedFieldOfHigherUnit`. -/
noncomputable def
    equalCharacteristicLubinTateLevelFieldEquivFixedFieldOfHigherUnit
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n) :
    @AlgEquiv
      F.residueField⸨X⸩
      ↥(equalCharacteristicLubinTateLevelField F n)
      ↥(equalCharacteristicCompletedFrobeniusFixedField F a n)
      inferInstance
      inferInstance
      inferInstance
      (equalCharacteristicLubinTateLevelFieldAlgebra F n)
      (equalCharacteristicCompletedFrobeniusFixedFieldAlgebra F a n) :=
  AlgEquiv.ofBijective
    (equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit F a n ha)
    ⟨fun _ _ h =>
      (equalCharacteristicLubinTateLevelFieldToCompletedRingHom F n).injective
        (congrArg Subtype.val h),
      equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit_surjective
        F a n ha⟩

end EqualCharacteristic
end LubinTate
