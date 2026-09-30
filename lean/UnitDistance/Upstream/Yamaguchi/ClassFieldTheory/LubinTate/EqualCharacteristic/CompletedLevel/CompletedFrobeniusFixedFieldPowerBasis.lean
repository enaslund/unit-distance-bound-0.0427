/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPrimitive

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# The completed theta-intertwining theorem: the fixed primitive completed power basis

The direct theta value supplies the power basis used to descend coefficients
of elements fixed by the prescribed completed Frobenius.
-/

noncomputable section

open scoped LaurentSeries Polynomial PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedFieldCompletedPowerBasisBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- Defines `equalCharacteristicDirectThetaCompletedPowerBasis`. -/
noncomputable def equalCharacteristicDirectThetaCompletedPowerBasis
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    PowerBasis (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) := by
  apply PowerBasis.ofAdjoinEqTop
    (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isIntegral_completedBase
      F a n)
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isIntegral_completedBase
        F a n).isAlgebraic,
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_adjoin_completedBase_eq_top,
    IntermediateField.top_toSubalgebra]

/-- States the theorem `equalCharacteristicDirectThetaCompletedPowerBasis_gen`. -/
@[simp]
theorem equalCharacteristicDirectThetaCompletedPowerBasis_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicDirectThetaCompletedPowerBasis F a n).gen =
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n) :=
  PowerBasis.ofAdjoinEqTop_gen _ _

end EqualCharacteristic
end LubinTate
