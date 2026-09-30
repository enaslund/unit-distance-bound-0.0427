/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Local conductor subgroups in the idele class group

This file records the one-place higher-unit subgroups used to compare
ray-class moduli with local conductors.  The constructions are
idele- and ray-class data and do not depend on the existence of a
global class field.
-/

open scoped NumberField

noncomputable section

namespace RayClass

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- The image in `C_K` of the `n`-th higher-unit group at `v`. -/
def localHigherUnitClassSubgroup
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (IdeleClassGroup K) :=
  (localHigherUnitGroup v n).map
    (IdeleGroup.finitePlaceIdeleClass v)

/-- A one-place higher-unit condition is contained in the corresponding
global ray congruence subgroup. -/
theorem localHigherUnitClassSubgroup_le_congruenceSubgroup
    (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K)) :
    localHigherUnitClassSubgroup v (m.finitePart v) ≤
      m.congruenceSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  change
    IdeleGroup.finitePlaceIdeleClass v x ∈
      m.congruenceSubgroup
  rw [Modulus.congruenceSubgroup]
  refine ⟨IdeleGroup.finitePlaceIdele v x, ?_, rfl⟩
  apply Subgroup.mem_sup_left
  rw [Modulus.mem_ideleCongruenceSubgroup_iff]
  refine
    ⟨m.infiniteCongruenceSubgroup.one_mem, ?_⟩
  rw [mem_finiteCongruenceSubgroup_iff]
  intro w
  change
    IdeleGroup.finiteComponent w
        (IdeleGroup.finitePlaceIdele v x) ∈
      localHigherUnitGroup w (m.finitePart w)
  by_cases hw : w = v
  · subst w
    rw [IdeleGroup.finitePlaceIdele_finiteComponent_same]
    change
      x ∈
        (localHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ)
    exact hx
  · rw [
      IdeleGroup.finitePlaceIdele_finiteComponent_of_ne
        v w x hw]
    exact (localHigherUnitGroup w (m.finitePart w)).one_mem

end RayClass
