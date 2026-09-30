/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import Mathlib.SetTheory.Cardinal.Finite
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.NormIndex

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Lubin--Tate application: the exact norm subgroup

The reusable Lubin--Tate layer proves containment of the standard subgroup and
computes its quotient.  Finite local reciprocity computes the norm-subgroup
index here, in the application layer, so the containment becomes an equality.
-/

noncomputable section

open scoped LaurentSeries ValuativeRel

namespace LubinTate
namespace EqualCharacteristic

open LocalClassFieldTheory

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable {K : Type} [Field K]

/-- The explicit norm-subgroup formula, with repository level `n` representing the canonical
level `n+1`: the norm subgroup is exactly `(T⁻¹) × U^(n+1)`. -/
theorem equalCharacteristicLubinTateNormSubgroup_eq_uniformizerPrincipalSubgroup
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    equalCharacteristicLubinTateNormSubgroup F n =
      LocalFieldTheory.uniformizerPrincipalSubgroup F.residueField⸨X⸩
        (equalCharacteristicLaurentUniformizerUnit F)⁻¹ 1 (n + 1) := by
  let B := F.residueField⸨X⸩
  let pi : Bˣ := (equalCharacteristicLaurentUniformizerUnit F)⁻¹
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let H := LocalFieldTheory.uniformizerPrincipalSubgroup B pi 1 (n + 1)
  let N := equalCharacteristicLubinTateNormSubgroup F n
  let d := (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n
  have hindexH : H.index = d := by
    rw [Subgroup.index_eq_card]
    simpa [B, H, pi, d] using
      (equalCharacteristicLubinTateUniformizerPrincipalQuotient_natCard F n)
  have hindexN : N.index = d := by
    simpa [N, d] using
      (equalCharacteristicLubinTateNormSubgroup_index F n)
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField))
      (Nat.pow_pos Nat.card_pos)
  let _ : H.FiniteIndex := ⟨by
    rw [hindexH]
    exact Nat.ne_of_gt hdpos⟩
  have hHN : H ≤ N := by
    exact
      equalCharacteristicLubinTate_uniformizerPrincipalSubgroup_le_normSubgroup
        F n
  apply Eq.symm
  apply le_antisymm hHN
  by_contra hNH
  have hne : H ≠ N := by
    intro heq
    apply hNH
    rw [heq]
  have hstrict : H < N := lt_of_le_of_ne hHN hne
  have hi := Subgroup.index_strictAnti hstrict
  rw [hindexH, hindexN] at hi
  exact Nat.lt_irrefl _ hi

end EqualCharacteristic
end LubinTate
