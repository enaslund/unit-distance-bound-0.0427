/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Unit cohomology under a field isomorphism

Conjugation identifies the automorphism groups, while the same field
isomorphism identifies their actual unit representations.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

/-- An actual algebra equivalence transports field-unit cohomology in every degree. -/
noncomputable def unitsCohomologyCongrTop
    (K L M : Type) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) (n : ℕ) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) n ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits K M) n :=
  groupCohomology.mapIso (AlgEquiv.autCongr e)
    (Units.mapEquiv e.toMulEquiv).toAdditive.toIntLinearEquiv (by
      intro σ
      apply LinearMap.ext
      intro x
      apply Units.ext
      change e (σ ((show Additive Lˣ from x).toMul : L)) =
        e (σ (e.symm (e ((show Additive Lˣ from x).toMul : L))))
      rw [e.symm_apply_apply]) n

end ClassFieldTower.Cohomology
