module

public import UnitDistance.DyadicDimension

@[expose] public section
set_option backward.privateInPublic true


/-! Exact finite certificates for the actual local dimension subgroups. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

noncomputable section
namespace UnitDistance.Dyadic.AlgebraD
open Filtration

theorem dimension_two_certificate : ∀ i,
    Graded.remainder b2 pivots2 (groupDifferenceVector i) = 0 ↔
      (D.ofIndex i).a = 0 ∧ (D.ofIndex i).b = 0 ∧ parity (D.ofIndex i).c = 0 := by
  decide +kernel

theorem dimension_three_certificate : ∀ i,
    Graded.remainder b3 pivots3 (groupDifferenceVector i) = 0 ↔ D.ofIndex i = 1 := by
  decide +kernel

theorem mem_dimensionSubgroup_two (g : D) : g ∈ dimensionSubgroup 2 ↔
    g.a = 0 ∧ g.b = 0 ∧ parity g.c = 0 := by
  obtain ⟨i, rfl⟩ := D.indexEquiv.symm.surjective g
  change delta (D.ofIndex i) - 1 ∈ augmentationPower 2 ↔ _
  rw [← coefficients_mem_stage, coefficients_group_difference, stage_2_eq,
    ← Graded.remainder_eq_zero_iff b2 pivots2 pivots2_correct]
  exact dimension_two_certificate i

theorem dimensionSubgroup_three : dimensionSubgroup 3 = ⊥ := by
  ext g
  obtain ⟨i, rfl⟩ := D.indexEquiv.symm.surjective g
  change delta (D.ofIndex i) - 1 ∈ augmentationPower 3 ↔ D.ofIndex i = 1
  rw [← coefficients_mem_stage, coefficients_group_difference, stage_3_eq,
    ← Graded.remainder_eq_zero_iff b3 pivots3 pivots3_correct]
  exact dimension_three_certificate i

/-- There are no augmentation dimension-subgroup layers above degree two. -/
theorem dimensionSubgroup_vanishes (n : ℕ) (hn : 3 ≤ n) : dimensionSubgroup n = ⊥ := by
  apply le_bot_iff.mp
  rw [← dimensionSubgroup_three]
  exact dimensionSubgroup_antitone hn

instance : DecidablePred (fun g : D => g ∈ dimensionSubgroup 2) := fun g =>
  decidable_of_iff (g.a = 0 ∧ g.b = 0 ∧ parity g.c = 0)
    (mem_dimensionSubgroup_two g).symm

theorem card_dimensionSubgroup_two : Fintype.card (dimensionSubgroup 2) = 4 := by
  decide +kernel

end UnitDistance.Dyadic.AlgebraD
