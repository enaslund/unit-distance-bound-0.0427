module

public import UnitDistance.GroupAugmentationHilbert
public import UnitDistance.JenningsGeneratedLayers
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
set_option backward.privateInPublic true


/-! Actual homogeneous group directions give the product formula for the
augmentation Hilbert polynomial through a proved weighted basis. -/
noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
open Polynomial

theorem binary_weight_sum_product (r : ℕ) (w : Fin r → ℕ) :
    (∑ c : Fin r → Bool,
      (Polynomial.monomial (JenningsCollection.binaryWeight r w c) 1 : ℕ[X]))=
      ∏ i, (1+X^(w i)) := by
  simp only [←Polynomial.C_mul_X_pow_eq_monomial,map_one,one_mul,
    JenningsCollection.binaryWeight,←Finset.prod_pow_eq_pow_sum]
  rw [←Fintype.prod_sum (fun (i : Fin r) (c : Bool) ↦
    (X : ℕ[X])^(if c then w i else 0))]
  apply Finset.prod_congr rfl
  intro i _
  simp [Fintype.sum_bool,add_comm]

theorem hilbertPolynomial_of_homogeneous_generators
    (G : Type*) [Group G] [Finite G] (hG : IsPGroup 2 G)
    (r : ℕ) (g : Fin r → G) (w : Fin r → ℕ)
    (hw : ∀ i,1≤w i) (hg : ∀ i,g i∈dimensionSubgroup (ZMod 2) G (w i))
    (hgen : ∀ n,1≤n → dimensionSubgroup (ZMod 2) G n≤
      Subgroup.closure {x | ∃ i,n≤w i ∧ x=g i})
    (hcard : 2^r=Nat.card G) : hilbertPolynomial G=∏ i,(1+X^(w i)) := by
  have hspan := spansActualLayers_of_generation G g w hg hgen
  let b := homogeneousBinaryBasis G hG r g w hw hg hspan hcard
  have hb (n : ℕ) : Submodule.span (ZMod 2)
      {a | ∃ c,n≤JenningsCollection.binaryWeight r w c ∧ a=b c}=power (ZMod 2) G n := by
    simp only [b,homogeneousBinaryBasis_apply]
    exact binarySpan_eq_power_of_spansActualLayers G hG r g w hw hg hspan n
  rw [hilbertPolynomial_eq_basisWeightSum G hG b
    (JenningsCollection.binaryWeight r w) hb,binary_weight_sum_product]

end UnitDistance.GroupAugmentation
