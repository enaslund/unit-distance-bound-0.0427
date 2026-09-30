/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerPrimeProduct
public import Mathlib.Topology.Algebra.Group.Units

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Units of the profinite integers

This file upgrades the prime-product Chinese-remainder equivalence for
`ℤ̂` to topological additive, multiplicative, and unit-group equivalences.
-/

open scoped Topology

noncomputable section

namespace ClassFormation

/-- The Chinese-remainder isomorphism as a topological monoid equivalence. -/
noncomputable def zHatContinuousMulEquivPrimeProduct :
    ZHat ≃ₜ* ProfiniteIntegerPrimeProduct :=
  ContinuousMulEquiv.mk'
    (continuous_zHatToProfiniteIntegerPrimeProduct.homeoOfEquivCompactToT2
      (f := zHatRingEquivProfiniteIntegerPrimeProduct.toEquiv))
    zHatRingEquivProfiniteIntegerPrimeProduct.map_mul

/-- The additive form of the topological Chinese-remainder isomorphism. -/
noncomputable def zHatContinuousAddEquivPrimeProduct :
    ZHat ≃ₜ+ ProfiniteIntegerPrimeProduct :=
  { zHatRingEquivProfiniteIntegerPrimeProduct.toAddEquiv with
    continuous_toFun :=
      zHatContinuousMulEquivPrimeProduct.continuous_toFun
    continuous_invFun :=
      zHatContinuousMulEquivPrimeProduct.continuous_invFun }

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- The canonical topological Chinese-remainder equivalence on unit
groups. -/
noncomputable def zHatUnitsContinuousMulEquivPrimeProduct :
    ZHatˣ ≃ₜ* ((p : Nat.Primes) → ℤ_[p.1]ˣ) :=
  (Units.mapContinuousMulEquiv
    zHatContinuousMulEquivPrimeProduct).trans
      ContinuousMulEquiv.piUnits

/-- On underlying ring elements, the unit-group Chinese-remainder
equivalence is the canonical `p`-adic coordinate map. -/
@[simp]
theorem zHatUnitsContinuousMulEquivPrimeProduct_coe_apply
    (u : ZHatˣ) (p : Nat.Primes) :
    (zHatUnitsContinuousMulEquivPrimeProduct u p : ℤ_[p.1]) =
      zHatToPadicInt p (u : ZHat) :=
  rfl

end ClassFormation
