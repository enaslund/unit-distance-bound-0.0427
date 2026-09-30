module

public import UnitDistance.GroupAugmentationLayerRanks
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
set_option backward.privateInPublic true


/-!
# Ordered representatives of actual binary dimension layers

A basis of the actual dimension-layer vector space is lifted to actual group
elements. Ordered products with binary exponents give a section of the
quotient map and a unique factorization into those products and the next
dimension subgroup. These are group normal forms; the assertion that all
corresponding augmentation monomials span the exact weighted powers remains
a separate Jennings obligation.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (G : Type*) [Group G] [Finite G] (n : ℕ) [hn : Fact (1 ≤ n)]

/-- An actual basis of the binary dimension layer. -/
def layerBasis : Module.Basis (Fin (layerRank G n)) (ZMod 2) (LayerVector G n) :=
  Module.finBasis (ZMod 2) (LayerVector G n)

/-- Each basis direction is lifted to an element of its actual dimension subgroup. -/
def layerBasisLift (i : Fin (layerRank G n)) : dimensionSubgroup (ZMod 2) G n :=
  (Additive.toMul (layerBasis G n i)).out

@[simp] theorem layerBasisLift_projection (i : Fin (layerRank G n)) :
    (QuotientGroup.mk' (layerDenominator (ZMod 2) G n)) (layerBasisLift G n i) =
      Additive.toMul (layerBasis G n i) := Quotient.out_eq' _

/-- A lifted basis direction has exactly its declared augmentation degree. -/
theorem layerBasisLift_not_mem_next (i : Fin (layerRank G n)) :
    (layerBasisLift G n i : G) ∉ dimensionSubgroup (ZMod 2) G (n+1) := by
  intro hi
  have hq : (QuotientGroup.mk' (layerDenominator (ZMod 2) G n)) (layerBasisLift G n i) = 1 :=
    (QuotientGroup.eq_one_iff (layerBasisLift G n i)).mpr hi
  rw [layerBasisLift_projection] at hq
  have hz : layerBasis G n i = 0 := congrArg Additive.ofMul hq
  exact (layerBasis G n).ne_zero i hz

theorem layerBasisLift_augmentation_degree (i : Fin (layerRank G n)) :
    delta (ZMod 2) (layerBasisLift G n i : G) - 1 ∈ power (ZMod 2) G n ∧
      delta (ZMod 2) (layerBasisLift G n i : G) - 1 ∉ power (ZMod 2) G (n+1) :=
  ⟨(layerBasisLift G n i).property, layerBasisLift_not_mem_next G n i⟩

/-- Products are taken in the actual group, in increasing basis-index order. -/
def orderedLayerSection (v : LayerVector G n) : dimensionSubgroup (ZMod 2) G n :=
  (List.ofFn (fun i : Fin (layerRank G n) =>
    layerBasisLift G n i ^ (((layerBasis G n).repr v i).val))).prod

/-- The ordered products are an actual section of the dimension-layer quotient. -/
theorem orderedLayerSection_projection (v : LayerVector G n) :
    (QuotientGroup.mk' (layerDenominator (ZMod 2) G n)) (orderedLayerSection G n v) =
      Additive.toMul v := by
  apply Additive.ofMul.injective
  change Additive.ofMul ((QuotientGroup.mk' (layerDenominator (ZMod 2) G n))
    ((List.ofFn (fun i : Fin (layerRank G n) =>
      layerBasisLift G n i ^ (((layerBasis G n).repr v i).val))).prod)) = v
  rw [map_list_prod, List.map_ofFn, List.prod_ofFn, ofMul_prod]
  simp only [Function.comp_apply]
  simp_rw [map_pow, layerBasisLift_projection, ofMul_pow, ofMul_toMul]
  have hs : ∀ i, (((layerBasis G n).repr v i).val) • layerBasis G n i =
      (layerBasis G n).repr v i • layerBasis G n i := by
    intro i
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
  simp_rw [hs]
  exact (layerBasis G n).sum_repr v

/-- Unique group factorization into an ordered binary product and an element
of the next actual dimension subgroup (viewed as a subgroup of this one). -/
def orderedLayerCoordinates :
    LayerVector G n × layerDenominator (ZMod 2) G n ≃ dimensionSubgroup (ZMod 2) G n :=
  Equiv.ofBijective (fun p => orderedLayerSection G n p.1 * p.2.val) (by
    constructor
    · rintro ⟨v,h⟩ ⟨v',h'⟩ he
      have hv : v = v' := by
        have hq := congrArg (QuotientGroup.mk' (layerDenominator (ZMod 2) G n)) he
        simp only [map_mul, orderedLayerSection_projection] at hq
        have hh : (QuotientGroup.mk' (layerDenominator (ZMod 2) G n)) h.val = 1 :=
          (QuotientGroup.eq_one_iff h.val).mpr h.property
        have hh' : (QuotientGroup.mk' (layerDenominator (ZMod 2) G n)) h'.val = 1 :=
          (QuotientGroup.eq_one_iff h'.val).mpr h'.property
        rw [hh,hh',mul_one,mul_one] at hq
        exact Additive.toMul.injective hq
      subst v'
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel he))
    · intro g
      let v : LayerVector G n :=
        Additive.ofMul ((QuotientGroup.mk' (layerDenominator (ZMod 2) G n)) g)
      have hh : (orderedLayerSection G n v)⁻¹ * g ∈ layerDenominator (ZMod 2) G n := by
        apply (QuotientGroup.eq_one_iff _).mp
        change (QuotientGroup.mk' (layerDenominator (ZMod 2) G n))
          ((orderedLayerSection G n v)⁻¹ * g) = 1
        rw [map_mul, map_inv, orderedLayerSection_projection]
        exact inv_mul_cancel _
      exact ⟨(v,⟨(orderedLayerSection G n v)⁻¹ * g,hh⟩), mul_inv_cancel_left _ _⟩)

/-- The next-subgroup factor can equivalently be written in its original
ambient group, so the normal form iterates down the actual filtration. -/
def orderedLayerCoordinatesNext :
    LayerVector G n × dimensionSubgroup (ZMod 2) G (n+1) ≃
      dimensionSubgroup (ZMod 2) G n :=
  (Equiv.prodCongr (Equiv.refl _) (layerDenominatorEquiv (R := ZMod 2) (G := G) (n := n)).symm.toEquiv).trans
    (orderedLayerCoordinates G n)

end UnitDistance.GroupAugmentation
