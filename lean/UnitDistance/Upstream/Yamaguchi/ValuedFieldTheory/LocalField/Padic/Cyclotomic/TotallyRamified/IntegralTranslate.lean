/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinRelation

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Translation of the integral ring in the totally ramified cyclotomic extension

This file records that translating `ζ` by one preserves the explicit integral closure.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open scoped Polynomial

universe u

section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

local instance padicCyclotomicTotallyRamifiedIntegralTranslateAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedIntegralTranslateScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Translating the generator by one does not change the explicit
`ℤ_[p]`-algebra. -/
theorem padicCyclotomicTotallyRamified_adjoin_sub_one_eq_adjoin
    (ζ : L) :
    Algebra.adjoin ℤ_[p] ({ζ - 1} : Set L) =
      Algebra.adjoin ℤ_[p] ({ζ} : Set L) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Subalgebra.sub_mem _
      (Algebra.self_mem_adjoin_singleton ℤ_[p] ζ)
      (Subalgebra.one_mem _)
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simpa using Subalgebra.add_mem _
      (Algebra.self_mem_adjoin_singleton ℤ_[p] (ζ - 1))
      (Subalgebra.one_mem _)

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
