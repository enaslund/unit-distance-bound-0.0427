/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Unit cohomology under surjective scalar restriction

When F → E is surjective, restricting an E-automorphism of N to F
is a group isomorphism. Its action on Nˣ is unchanged.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

/-- Restricting scalars along a surjective base-field map preserves unit
cohomology, with identity coefficients in the unchanged top field. -/
noncomputable def unitsCohomologyRestrictScalarsIso
    (F E N : Type) [Field F] [Field E] [Field N]
    [Algebra F E] [Algebra E N] [Algebra F N] [IsScalarTower F E N]
    (h : Function.Surjective (algebraMap F E)) (n : ℕ) :
    groupCohomology (Rep.ofAlgebraAutOnUnits E N) n ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits F N) n :=
  groupCohomology.mapIso
    (AlgEquiv.extendScalarsHomOfSurjective (A := N) h).symm
    (LinearEquiv.refl ℤ (Additive Nˣ)) (fun _ ↦ rfl) n

end ClassFieldTower.Cohomology
