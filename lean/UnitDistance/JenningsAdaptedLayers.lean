module

public import UnitDistance.JenningsFilteredBasis
public import UnitDistance.GroupAugmentationDyadicRanks
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual layer bases adapted to a prescribed local group homomorphism

Injectivity of an actual dimension-layer map allows extension of its actual
local basis. The ambient lifts of the local basis vectors are prescribed to
be the original local group representatives mapped into the ambient group.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (D P : Type*) [Group D] [Group P] [Finite D]
variable (f : D →* P) (n : ℕ) [Fact (1 ≤ n)]
variable (hinj : Function.Injective (layerMap (ZMod 2) D f n))

include hinj in
/-- Images of the actual local layer basis are independent in the ambient layer. -/
theorem mappedLayerBasis_independent :
    LinearIndependent (ZMod 2) (fun i => layerLinearMap D n f (layerBasis D n i)) :=
  (layerBasis D n).linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hinj)

/-- The extra vectors added when extending the genuine local layer basis. -/
abbrev LayerComplement := Module.Basis.sumExtendIndex (mappedLayerBasis_independent D P f n hinj)

/-- The actual ambient layer basis, with complementary indices before local indices. -/
def adaptedLayerBasis : Module.Basis (LayerComplement D P f n hinj ⊕ Fin (layerRank D n))
    (ZMod 2) (LayerVector P n) :=
  (Module.Basis.sumExtend (mappedLayerBasis_independent D P f n hinj)).reindex
    (Equiv.sumComm _ _)

@[simp] theorem adaptedLayerBasis_inr (i : Fin (layerRank D n)) :
    adaptedLayerBasis D P f n hinj (Sum.inr i) = layerLinearMap D n f (layerBasis D n i) := by
  rw [adaptedLayerBasis, Module.Basis.reindex_apply]
  change Module.Basis.sumExtend (mappedLayerBasis_independent D P f n hinj)
      (Sum.inl i) = _
  rw [Module.Basis.sumExtend, Module.Basis.reindex_apply]
  dsimp only [Module.Basis.sumExtendIndex]
  simp only [Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply,
    Equiv.Set.sumDiffSubset_apply_inl, Equiv.ofInjective_apply,
    Set.inclusion_mk]
  exact Module.Basis.extend_apply_self _ _

/-- Lift complementary vectors arbitrarily, but preserve the actual mapped
local group representatives literally. -/
def adaptedLayerLift : (LayerComplement D P f n hinj ⊕ Fin (layerRank D n)) →
    dimensionSubgroup (ZMod 2) P n
  | Sum.inl i => (Additive.toMul (adaptedLayerBasis D P f n hinj (Sum.inl i))).out
  | Sum.inr i => dimensionHom (ZMod 2) D f n (layerBasisLift D n i)

@[simp] theorem adaptedLayerLift_inr (i : Fin (layerRank D n)) :
    (adaptedLayerLift D P f n hinj (Sum.inr i) : P) = f (layerBasisLift D n i) := rfl

/-- Every chosen lift represents the actual extended layer basis vector. -/
theorem adaptedLayerLift_projection
    (i : LayerComplement D P f n hinj ⊕ Fin (layerRank D n)) :
    Additive.ofMul (QuotientGroup.mk (adaptedLayerLift D P f n hinj i)) =
      adaptedLayerBasis D P f n hinj i := by
  cases i with
  | inl i =>
    exact congrArg Additive.ofMul (Quotient.out_eq' _)
  | inr i =>
    rw [adaptedLayerBasis_inr]
    change Additive.ofMul (layerMap (ZMod 2) D f n (QuotientGroup.mk (layerBasisLift D n i))) = _
    have he : QuotientGroup.mk (layerBasisLift D n i) = Additive.toMul (layerBasis D n i) :=
      layerBasisLift_projection D n i
    rw [he]
    rfl

/-- The adapted representatives have their exact actual ambient augmentation degree. -/
theorem adaptedLayerLift_not_mem_next
    (i : LayerComplement D P f n hinj ⊕ Fin (layerRank D n)) :
    (adaptedLayerLift D P f n hinj i : P) ∉ dimensionSubgroup (ZMod 2) P (n+1) := by
  intro hi
  have hq : (QuotientGroup.mk' (layerDenominator (ZMod 2) P n))
      (adaptedLayerLift D P f n hinj i) = 1 :=
    (QuotientGroup.eq_one_iff (adaptedLayerLift D P f n hinj i)).mpr hi
  have hz := congrArg Additive.ofMul hq
  change Additive.ofMul (QuotientGroup.mk (adaptedLayerLift D P f n hinj i)) = 0 at hz
  rw [adaptedLayerLift_projection] at hz
  exact (adaptedLayerBasis D P f n hinj).ne_zero i hz

/-- The chosen adapted group lifts have the intended actual degree. -/
theorem adaptedLayerLift_degree [Finite P] (hP : IsPGroup 2 P)
    (i : LayerComplement D P f n hinj ⊕ Fin (layerRank D n)) :
    groupDegree P hP (adaptedLayerLift D P f n hinj i : P) = n :=
  groupDegree_eq_of_mem_not_mem P hP _ n (adaptedLayerLift D P f n hinj i).property
    (adaptedLayerLift_not_mem_next D P f n hinj i)

/-- The number of complementary layer directions is the exact rank difference. -/
theorem card_layerComplement_add_rank [Finite P] :
    Nat.card (LayerComplement D P f n hinj) + layerRank D n = layerRank P n := by
  letI : Fintype (LayerComplement D P f n hinj) := Fintype.ofFinite _
  have he := Module.finrank_eq_card_basis (adaptedLayerBasis D P f n hinj)
  change layerRank P n = _ at he
  rw [Fintype.card_sum,Fintype.card_fin,← Nat.card_eq_fintype_card] at he
  exact he.symm

@[simp] theorem layerLinearEmbedding_adaptedBasis
    (i : LayerComplement D P f n hinj ⊕ Fin (layerRank D n)) :
    layerLinearEmbedding P n (adaptedLayerBasis D P f n hinj i) =
      (power (ZMod 2) P (n+1)).mkQ
        (delta (ZMod 2) (adaptedLayerLift D P f n hinj i : P)-1) := by
  rw [← adaptedLayerLift_projection]
  rfl

/-- Actual homogeneous coefficients in the extended basis, including the
literally prescribed local representatives. -/
def adaptedInitialDifference [Finite P]
    (g : dimensionSubgroup (ZMod 2) P n) : A (ZMod 2) P := by
  letI : Fintype (LayerComplement D P f n hinj ⊕ Fin (layerRank D n)) := Fintype.ofFinite _
  exact ∑ i, (adaptedLayerBasis D P f n hinj).repr (Additive.ofMul (QuotientGroup.mk g)) i •
    (delta (ZMod 2) (adaptedLayerLift D P f n hinj i : P)-1)

/-- The adapted linear expansion has its error in the next actual power. -/
theorem difference_sub_adaptedInitial_mem [Finite P]
    (g : dimensionSubgroup (ZMod 2) P n) :
    delta (ZMod 2) (g : P)-1-adaptedInitialDifference D P f n hinj g ∈
      power (ZMod 2) P (n+1) := by
  letI : Fintype (LayerComplement D P f n hinj ⊕ Fin (layerRank D n)) := Fintype.ofFinite _
  have he := congrArg (layerLinearEmbedding P n)
    ((adaptedLayerBasis D P f n hinj).sum_repr (Additive.ofMul (QuotientGroup.mk g)))
  simp only [map_sum,map_smul,layerLinearEmbedding_adaptedBasis,layerLinearEmbedding_mk] at he
  apply (Submodule.Quotient.eq _).mp
  change (power (ZMod 2) P (n+1)).mkQ (delta (ZMod 2) (g : P)-1) =
    (power (ZMod 2) P (n+1)).mkQ (adaptedInitialDifference D P f n hinj g)
  rw [adaptedInitialDifference,map_sum]
  simp only [map_smul]
  exact he.symm

end UnitDistance.GroupAugmentation
