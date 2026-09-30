/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import Mathlib.SetTheory.Cardinal.Finite
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# The equal-characteristic completed-unramified construction: equal-characteristic Frobenius on the completed unramified ring

For a finite field `k`, arithmetic Frobenius acts on `AlgebraicClosure k`
by the `#k`-power map and hence coefficientwise on
`(AlgebraicClosure k)[[T]]`.  These definitions belong to the completed
maximal-unramified source used in the equal-characteristic completed-unramified construction; the theta construction of the equal-characteristic theta construction
depends on them, not conversely.

This is an equal-characteristic specialization of the general local-field construction, not a claim that Lemma the equal-characteristic completed-unramified construction is complete in general.
-/

noncomputable section

open scoped PowerSeries

universe u

namespace LubinTate
namespace EqualCharacteristic

variable (k : Type u) [Field k] [Finite k]

/-- Arithmetic Frobenius on the algebraic closure of the finite coefficient
field. -/
noncomputable def equalCharacteristicCoefficientFrobenius :
    AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k := by
  letI : Fintype k := Fintype.ofFinite k
  exact FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)

/-- States the theorem `equalCharacteristicCoefficientFrobenius_apply`. -/
@[simp]
theorem equalCharacteristicCoefficientFrobenius_apply
    (x : AlgebraicClosure k) :
    equalCharacteristicCoefficientFrobenius k x = x ^ Nat.card k := by
  let : Fintype k := Fintype.ofFinite k
  simp [equalCharacteristicCoefficientFrobenius,
    Nat.card_eq_fintype_card]

/-- Arithmetic Frobenius on the completed maximal-unramified coefficient
ring, acting coefficientwise and fixing `T`. -/
noncomputable def equalCharacteristicPowerSeriesFrobenius :
    (AlgebraicClosure k)⟦X⟧ →+* (AlgebraicClosure k)⟦X⟧ :=
  PowerSeries.map (equalCharacteristicCoefficientFrobenius k).toRingHom

/-- States the theorem `equalCharacteristicPowerSeriesFrobenius_coeff`. -/
@[simp]
theorem equalCharacteristicPowerSeriesFrobenius_coeff
    (f : (AlgebraicClosure k)⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (equalCharacteristicPowerSeriesFrobenius k f) =
      (PowerSeries.coeff n f) ^ Nat.card k := by
  simp [equalCharacteristicPowerSeriesFrobenius,
    equalCharacteristicCoefficientFrobenius_apply]

/-- States the theorem `equalCharacteristicPowerSeriesFrobenius_X`. -/
@[simp]
theorem equalCharacteristicPowerSeriesFrobenius_X :
    equalCharacteristicPowerSeriesFrobenius k
        (PowerSeries.X : (AlgebraicClosure k)⟦X⟧) =
      PowerSeries.X := by
  simp [equalCharacteristicPowerSeriesFrobenius]

end EqualCharacteristic
end LubinTate
