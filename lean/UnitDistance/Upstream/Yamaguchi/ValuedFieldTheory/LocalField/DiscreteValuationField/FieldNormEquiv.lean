/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNorm

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Field-norm subgroups under algebra equivalence

An algebra equivalence over the base field preserves the field norm and
therefore identifies the corresponding norm subgroups of the base unit
group.
-/

noncomputable section

universe u v w

namespace LocalFieldTheory.DiscreteValuationField

variable (K : Type u) (L : Type v) (E : Type w)
variable [Field K] [Field L] [Field E]
variable [Algebra K L] [Algebra K E]

/-- Mapping a unit through a base-field algebra equivalence does not change
its field norm. -/
theorem fieldNormUnits_map_algEquiv
    (e : L ≃ₐ[K] E) (z : Lˣ) :
    normUnits K E
        (Units.map e.toRingEquiv.toMonoidHom z) =
      normUnits K L z := by
  apply Units.ext
  change
    Algebra.norm K (e (z : L)) =
      Algebra.norm K (z : L)
  exact Algebra.norm_eq_of_algEquiv e (z : L)

/-- Base-field algebra-equivalent extensions have the same norm subgroup. -/
theorem fieldNormSubgroup_eq_of_algEquiv
    (e : L ≃ₐ[K] E) :
    fieldNormSubgroup K L = fieldNormSubgroup K E := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine
      ⟨Units.map e.toRingEquiv.toMonoidHom z, ?_⟩
    exact fieldNormUnits_map_algEquiv K L E e z
  · rintro ⟨z, rfl⟩
    refine
      ⟨Units.map e.symm.toRingEquiv.toMonoidHom z, ?_⟩
    exact fieldNormUnits_map_algEquiv K E L e.symm z

end LocalFieldTheory.DiscreteValuationField

end
