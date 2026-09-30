/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldAlgebra

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# LubinTate the explicit norm-subgroup computation: the standard level embedded in the higher-unit fixed field

For a coefficient unit in `U^(n+1)`, the standard completed-level embedding
lands in the completed theta-intertwining theorem fixed field.  This leaf packages its canonical
codomain restriction for the finite-dimensional comparison.
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

/-- The canonical standard-level embedding into the fixed field attached to
a higher unit, regarded as a ring homomorphism.  This lightweight helper
keeps the codomain restriction independent of algebra-instance search. -/
noncomputable def
    equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnitRingHom
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n) :
    equalCharacteristicLubinTateLevelField F n →+*
      equalCharacteristicCompletedFrobeniusFixedField F a n :=
  (equalCharacteristicLubinTateLevelFieldToCompletedRingHom F n).codRestrict
    (equalCharacteristicCompletedFrobeniusFixedFieldSubring F a n)
    (equalCharacteristicLubinTateLevelFieldToCompleted_mem_fixedField_of_mem_higherUnit
      F a n ha)

/-- The canonical standard-level algebra embedding into the fixed field
attached to a higher unit. -/
noncomputable def equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n) :
    @AlgHom
      F.residueField⸨X⸩
      ↥(equalCharacteristicLubinTateLevelField F n)
      ↥(equalCharacteristicCompletedFrobeniusFixedField F a n)
      inferInstance
      inferInstance
      inferInstance
      (equalCharacteristicLubinTateLevelFieldAlgebra F n)
      (equalCharacteristicCompletedFrobeniusFixedFieldAlgebra F a n) :=
  AlgHom.mk
    (equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnitRingHom
      F a n ha)
    (fun b => Subtype.ext
      (equalCharacteristicLubinTateLevelFieldToCompletedRingHom_algebraMap F n b))

end EqualCharacteristic
end LubinTate
