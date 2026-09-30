module

public import UnitDistance.GroupAugmentationLog
public import UnitDistance.GroupAugmentationNilpotence
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.Coset.Card

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual binary dimension layers as vector spaces

Each positive augmentation dimension layer is abelian and, in characteristic
two, has exponent two. It therefore carries its canonical `𝔽₂` vector-space
structure, faithfully embedded in the actual augmentation algebra quotient.
This supplies homogeneous vector spaces and their ranks for a future
ambient Jennings basis construction.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G] (n : ℕ) [hn : Fact (1 ≤ n)]

/-- Squaring on a positive characteristic-two dimension layer is trivial. -/
theorem layer_sq_eq_one [CharP R 2] (x : Layer R G n) : x^2 = 1 := by
  apply layerEmbedding_injective R G n hn.out
  rw [map_pow, map_one, pow_two]
  change (Multiplicative.toAdd (layerEmbedding R G n hn.out x)) +
    (Multiplicative.toAdd (layerEmbedding R G n hn.out x)) = 0
  rw [← two_smul R, CharTwo.two_eq_zero, zero_smul]

instance layerCommGroup : CommGroup (Layer R G n) :=
  MonoidHom.commGroupOfInjective (layerEmbedding R G n hn.out)
    (layerEmbedding_injective R G n hn.out)


/-- The additive notation for the actual binary quotient group. -/
abbrev LayerVector := Additive (Layer (ZMod 2) G n)

instance layerVectorModule : Module (ZMod 2) (LayerVector G n) :=
  AddCommGroup.zmodModule (n := 2) (fun x => by
    change (Additive.toMul x)^2 = 1
    exact layer_sq_eq_one (ZMod 2) G n (Additive.toMul x))

/-- The group-difference injection is actually linear for the canonical
binary vector-space structure. -/
def layerLinearEmbedding : LayerVector G n →ₗ[ZMod 2] AugmentationQuotient (ZMod 2) G n :=
  ((layerEmbedding (ZMod 2) G n hn.out).toAdditiveLeft).toZModLinearMap 2

theorem layerLinearEmbedding_injective : Function.Injective (layerLinearEmbedding G n) := by
  intro x y h
  exact layerEmbedding_injective (ZMod 2) G n hn.out h

/-- The ordinary dimension of this actual group layer. -/
def layerRank : ℕ := Module.finrank (ZMod 2) (LayerVector G n)

/-- The layer has precisely `2^rank` elements; no rank is specified by fiat. -/
theorem card_layer [Finite G] : Nat.card (Layer (ZMod 2) G n) = 2 ^ layerRank G n := by
  letI : Fintype (LayerVector G n) := Fintype.ofFinite _
  change Nat.card (LayerVector G n) = 2 ^ layerRank G n
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rfl

variable {H : Type*} [Group H]

/-- The genuine group-layer homomorphism is linear for these canonical
binary vector-space structures. -/
def layerLinearMap (f : G →* H) : LayerVector G n →ₗ[ZMod 2] LayerVector H n :=
  ((layerMap (ZMod 2) G f n).toAdditive).toZModLinearMap 2

theorem layerLinearMap_injective_iff (f : G →* H) :
    Function.Injective (layerLinearMap G n f) ↔
      Function.Injective (layerMap (ZMod 2) G f n) := Iff.rfl

variable {R G n}

/-- The next subgroup, regarded inside the current dimension subgroup,
is canonically the original next subgroup. -/
def layerDenominatorEquiv : layerDenominator R G n ≃* dimensionSubgroup R G (n+1) where
  toFun g := ⟨g.val.val, g.property⟩
  invFun g := ⟨⟨g.val, dimensionSubgroup_antitone R G (Nat.le_succ n) g.property⟩, g.property⟩
  left_inv g := by cases g; rfl
  right_inv g := by cases g; rfl
  map_mul' _ _ := rfl

/-- The actual cardinality step along the dimension filtration. -/
theorem card_dimensionSubgroup_step [Finite G] :
    Nat.card (dimensionSubgroup (ZMod 2) G n) =
      2 ^ layerRank G n * Nat.card (dimensionSubgroup (ZMod 2) G (n+1)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (layerDenominator (ZMod 2) G n)]
  rw [card_layer G n]
  congr 1
  exact Nat.card_congr (layerDenominatorEquiv (R := ZMod 2) (G := G) (n := n)).toEquiv

variable (G)

/-- Zero-indexed list of the ranks of the positive actual binary layers. -/
def positiveLayerRank (i : ℕ) : ℕ := by
  letI : Fact (1 ≤ i+1) := ⟨Nat.succ_le_succ (Nat.zero_le i)⟩
  exact layerRank G (i+1)

theorem card_dimensionSubgroup_positive_step [Finite G] (i : ℕ) :
    Nat.card (dimensionSubgroup (ZMod 2) G (i+1)) =
      2 ^ positiveLayerRank G i * Nat.card (dimensionSubgroup (ZMod 2) G (i+2)) := by
  letI : Fact (1 ≤ i+1) := ⟨Nat.succ_le_succ (Nat.zero_le i)⟩
  exact card_dimensionSubgroup_step (G := G) (n := i+1)

/-- Multiplying actual successive quotient cardinalities telescopes. -/
theorem card_dimensionSubgroup_telescope [Finite G] (N : ℕ) :
    Nat.card G = 2 ^ (∑ i ∈ Finset.range N, positiveLayerRank G i) *
      Nat.card (dimensionSubgroup (ZMod 2) G (N+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, card_dimensionSubgroup_positive_step G N, Finset.sum_range_succ, pow_add,
      mul_assoc]

/-- For a finite 2-group the ranks of all its positive actual dimension
layers add up to the binary logarithm of its order, expressed without
logarithms. Termination here is proved from augmentation nilpotence. -/
theorem card_eq_two_pow_sum_layerRanks [Finite G] (hG : IsPGroup 2 G) :
    Nat.card G = 2 ^ (∑ i ∈ Finset.range (Nat.card G), positiveLayerRank G i) := by
  have ht := card_dimensionSubgroup_telescope G (Nat.card G)
  rw [dimensionSubgroup_eq_bot_of_card_le G 2 hG (Nat.card G+1) (Nat.le_succ _),
    Subgroup.card_bot, mul_one] at ht
  exact ht

end UnitDistance.GroupAugmentation
