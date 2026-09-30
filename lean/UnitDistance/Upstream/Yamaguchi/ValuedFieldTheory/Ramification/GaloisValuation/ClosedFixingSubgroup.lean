/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Closed fixing subgroups

This module packages the closed subgroup attached to an intermediate field in
the Krull topology.
-/

noncomputable section

namespace RamificationTheory

/-- The closed fixing subgroup attached to an intermediate field. -/
@[implicit_reducible]
noncomputable def closedFixingSubgroup
    (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) : ClosedSubgroup Gal(Ω/k) :=
  ⟨K.fixingSubgroup, InfiniteGalois.fixingSubgroup_isClosed K⟩

end RamificationTheory
