/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch. The Mathlib
4.35 Denumerable import relocation is recorded in
third-party/yamaguchi/lean-v4.35-migration.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import Mathlib.Topology.Algebra.Valued.ValuativeRel

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Valued-field topology and the induced valuative relation

This file records the topology bridge used when a nonarchimedean norm is
turned into a `ValuativeRel`: the topology already carried by a nontrivially
valued field is the valuative topology for that induced relation.
-/

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel

universe u v

/-- The topology of a nontrivially valued field is valuative for the
valuative relation induced by its distinguished valuation. -/
theorem isValuativeTopology_of_valued_ofValuation
    (F : Type u) (Γ : Type v)
    [Field F] [LinearOrderedCommGroupWithZero Γ]
    [MulArchimedean Γ] [Valued F Γ]
    [Valuation.IsNontrivial (Valued.v : Valuation F Γ)] :
    letI := ValuativeRel.ofValuation (Valued.v : Valuation F Γ)
    IsValuativeTopology F := by
  let v : Valuation F Γ := Valued.v
  let : ValuativeRel F := ValuativeRel.ofValuation v
  let : v.Compatible := Valuation.Compatible.ofValuation v
  let : ValuativeRel.IsNontrivial F :=
    (ValuativeRel.isNontrivial_iff_isNontrivial v).2 inferInstance
  apply IsValuativeTopology.of_zero
  intro s
  rw [Valued.mem_nhds_zero]
  simpa [sub_zero] using
    (Valuation.exists_setOfPred_restrict_le_iff
      (v := v) (x := (0 : F)) (s := s))

end LocalFieldTheory
