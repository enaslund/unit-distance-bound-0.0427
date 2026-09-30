module

public import UnitDistance.GroupAugmentationDyadic
public import UnitDistance.GroupAugmentationLayerRanks

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual two local dyadic layer dimensions

The generic quotient vector spaces have dimensions three and two for the
paper's concrete dyadic group. These follow from the previously checked
actual dimension-subgroup cardinalities, not from an assigned Hilbert rank.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
open Dyadic

local instance : Fact (1 ≤ (1 : ℕ)) := ⟨by decide⟩
local instance : Fact (1 ≤ (2 : ℕ)) := ⟨by decide⟩

theorem dyadic_card_dimension_one : Nat.card (dimensionSubgroup F D 1) = 32 := by
  rw [dimensionSubgroup_one, Subgroup.card_top, Nat.card_eq_fintype_card, D.card]

theorem dyadic_card_dimension_two : Nat.card (dimensionSubgroup F D 2) = 4 := by
  rw [dyadic_dimensionSubgroup, Nat.card_eq_fintype_card,
    AlgebraD.card_dimensionSubgroup_two]

theorem dyadic_card_dimension_three : Nat.card (dimensionSubgroup F D 3) = 1 := by
  rw [dyadic_dimensionSubgroup_three, Subgroup.card_bot]

/-- The actual degree-one quotient vector space has dimension three. -/
theorem dyadic_layerRank_one : layerRank D 1 = 3 := by
  have ht := card_dimensionSubgroup_step (G := D) (n := 1)
  rw [dyadic_card_dimension_one, dyadic_card_dimension_two] at ht
  apply Nat.pow_right_injective (show 2 ≤ 2 from le_refl _)
  change 2 ^ layerRank D 1 = 2^3
  norm_num at ht ⊢
  omega

/-- The actual degree-two quotient vector space has dimension two. -/
theorem dyadic_layerRank_two : layerRank D 2 = 2 := by
  have ht := card_dimensionSubgroup_step (G := D) (n := 2)
  rw [dyadic_card_dimension_two, dyadic_card_dimension_three, mul_one] at ht
  apply Nat.pow_right_injective (show 2 ≤ 2 from le_refl _)
  exact ht.symm

variable {P : Type*} [Group P] [Finite P]

/-- Faithful degree-one realization requires at least three actual ambient
homogeneous directions. This is an ordinary vector-space rank inequality. -/
theorem dyadic_three_le_ambient_layerRank (f : D →* P)
    (hf : Function.Injective (layerMap F D f 1)) : 3 ≤ layerRank P 1 := by
  calc
    3 = layerRank D 1 := dyadic_layerRank_one.symm
    _ ≤ layerRank P 1 := (layerLinearMap D 1 f).finrank_le_finrank_of_injective hf

/-- The two actual degree-two directions are likewise retained in the
ambient quotient whenever its genuine layer map is injective. -/
theorem dyadic_two_le_ambient_layerRank (f : D →* P)
    (hf : Function.Injective (layerMap F D f 2)) : 2 ≤ layerRank P 2 := by
  calc
    2 = layerRank D 2 := dyadic_layerRank_two.symm
    _ ≤ layerRank P 2 := (layerLinearMap D 2 f).finrank_le_finrank_of_injective hf

end UnitDistance.GroupAugmentation
