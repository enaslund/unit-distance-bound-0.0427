/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalExact
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalModule
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Fintype.Card

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# The ideal-square radical over the rationals

Class number one makes the actual unit-to-radical map surjective.
The integral units of the rationals are ±1, so these two representatives
exhaust the ideal-square radical. This identifies its unique possible
obstruction coordinate without assuming a dimension bound or a comparison.
-/

open NumberField IsDedekindDomain
open scoped NumberField

namespace ClassFieldTower.Sawin
open ClassFieldTower.Martinet.Shafarevich

private theorem rationalRingUnit_eq_one_or_neg_one (u : (𝓞 ℚ)ˣ) :
    u = 1 ∨ u = -1 := by
  let e : (𝓞 ℚ)ˣ ≃* ℤˣ := Units.mapEquiv Rat.ringOfIntegersEquiv.toMulEquiv
  rcases Int.units_eq_one_or (e u) with h | h
  · exact Or.inl (e.injective (h.trans (map_one e).symm))
  · right
    apply e.injective
    have hNeg : e (-1) = -1 := by
      apply Units.ext
      change Rat.ringOfIntegersEquiv (-1) = -1
      rw [map_neg, map_one]
    exact h.trans hNeg.symm

private theorem rationalIntegralUnitToIdealSquareRadical_surjective :
    Function.Surjective (integralUnitToIdealNthPowerRadicalQuotient ℚ (2 : ℕ+)) := by
  have hClass : Subsingleton (ClassGroup (𝓞 ℚ)) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq Rat.classNumber_eq)
  intro x
  have hKer : x ∈ (idealNthPowerRadicalToClassTorsion ℚ (2 : ℕ+)).ker := by
    apply Subtype.ext
    exact hClass.elim _ _
  rw [← range_ordinaryUnitToIdealRadical_eq_ker_toClassTorsion ℚ (2 : ℕ+)] at hKer
  obtain ⟨u, hu⟩ := hKer
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
  exact ⟨v, hu⟩

/-- Every element of the rational ideal-square radical is zero or the
actual class of the integral unit −1. -/
theorem rationalIdealSquareRadical_eq_zero_or_neg_one
    (x : idealPowerRadicalModP ℚ 2) :
    x = 0 ∨ x = Additive.ofMul
      (integralUnitToIdealNthPowerRadicalQuotient ℚ (2 : ℕ+) (-1)) := by
  obtain ⟨u, hu⟩ := rationalIntegralUnitToIdealSquareRadical_surjective (Additive.toMul x)
  rcases rationalRingUnit_eq_one_or_neg_one u with h | h
  · left
    apply Additive.toMul.injective
    rw [h, map_one] at hu
    exact hu.symm
  · right
    apply Additive.toMul.injective
    rw [h] at hu
    exact hu.symm

end ClassFieldTower.Sawin
