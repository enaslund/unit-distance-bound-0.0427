/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section
set_option backward.privateInPublic true


/-!
# Field norms on unit groups

This file provides the common algebraic norm map on unit groups.  It is
independent of any valuation or local-field structure, so valued-field and
discrete-valuation APIs can share the same definition.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u v w

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- The algebra norm, restricted to unit groups. -/
def normUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- The underlying field element of a unit norm is the algebra norm. -/
@[simp]
theorem normUnits_apply_coe (x : Lˣ) :
    ((normUnits K L x : Kˣ) : K) = Algebra.norm K (x : L) :=
  rfl

/-- Field norms on unit groups are transitive in a tower. -/
theorem normUnits_tower
    (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [Module.Free M L] (x : Lˣ) :
    normUnits K M (normUnits M L x) = normUnits K L x := by
  apply Units.ext
  exact Algebra.norm_norm

end

end LocalFieldTheory
