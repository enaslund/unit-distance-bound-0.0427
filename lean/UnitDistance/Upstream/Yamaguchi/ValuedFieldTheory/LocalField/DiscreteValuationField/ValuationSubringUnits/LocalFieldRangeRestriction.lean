/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Multiplicative-range restriction for local fields

This file packages range restriction as a `LocalField` and exposes the
properness and completeness of the resulting topology.
-/

noncomputable section

universe u v

open scoped Valued

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace LocalField

variable {K : Type u} [Field K]

/-- A local-field package with its chosen valuation restricted to the actual
multiplicative range. -/
def mrangeRestrict (F : LocalField.{u, v} K) :
    LocalField.{u, v} K := by
  let G : CompleteDVF.{u, v} K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictCompleteDVF F.toCompleteDVF)
  haveI : Finite G.residueField := by
    simpa [G, CompleteDVF.mrangeRestrictCompleteDVF,
      CompleteDVF.residueField, CompleteDVF.valuationSubring,
      CompleteDVF.toDVF] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_residueField_finite F.toCompleteDVF)
  exact { toCompleteDVF := G }

/-- The range-restricted topology attached to a local-field package is proper. -/
theorem mrangeRestrict_properSpace
    (F : LocalField.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange
          F.toCompleteDVF.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF)
    ProperSpace K := by
  exact
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_properSpace_of_residueField_finite F.toCompleteDVF)

/-- The range-restricted topology attached to a local-field package is complete. -/
theorem mrangeRestrict_completeSpace
    (F : LocalField.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange
          F.toCompleteDVF.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF)
    CompleteSpace K := by
  exact
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_completeSpace_of_residueField_finite F.toCompleteDVF)


end LocalField
end LocalFieldTheory.DiscreteValuationField

end
