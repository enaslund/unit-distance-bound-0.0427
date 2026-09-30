module

public import UnitDistance.JenningsLayerNormalForm

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual initial forms of group differences, commutators and squares

Every group difference in degree n is expanded modulo the actual next
augmentation power in the actual lifted basis of its dimension layer.
Commutators and squares give degree-preserving linear replacement relations
modulo the next power. These are the algebraic collection relations needed
for the remaining weighted Jennings spanning proof.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (G : Type*) [Group G] [Finite G] (n : ℕ) [hn : Fact (1 ≤ n)]

omit [Finite G] in
@[simp] theorem layerLinearEmbedding_mk (g : dimensionSubgroup (ZMod 2) G n) :
    layerLinearEmbedding G n (Additive.ofMul (QuotientGroup.mk g)) =
      (power (ZMod 2) G (n+1)).mkQ (delta (ZMod 2) (g : G)-1) := rfl

@[simp] theorem layerLinearEmbedding_basis (i : Fin (layerRank G n)) :
    layerLinearEmbedding G n (layerBasis G n i) =
      (power (ZMod 2) G (n+1)).mkQ (delta (ZMod 2) (layerBasisLift G n i : G)-1) := by
  have hv : Additive.ofMul (QuotientGroup.mk (layerBasisLift G n i)) = layerBasis G n i :=
    congrArg Additive.ofMul (layerBasisLift_projection G n i)
  rw [← hv, layerLinearEmbedding_mk]

/-- The actual homogeneous linear combination representing a group element's
initial difference. Its coefficients come from the actual quotient-vector basis. -/
def initialDifference (g : dimensionSubgroup (ZMod 2) G n) : A (ZMod 2) G :=
  ∑ i, (layerBasis G n).repr (Additive.ofMul (QuotientGroup.mk g)) i •
    (delta (ZMod 2) (layerBasisLift G n i : G)-1)

/-- The remainder is in the next actual augmentation power. -/
theorem difference_sub_initial_mem (g : dimensionSubgroup (ZMod 2) G n) :
    delta (ZMod 2) (g : G)-1 - initialDifference G n g ∈ power (ZMod 2) G (n+1) := by
  have he := congrArg (layerLinearEmbedding G n)
    ((layerBasis G n).sum_repr (Additive.ofMul (QuotientGroup.mk g)))
  simp only [map_sum, map_smul, layerLinearEmbedding_basis, layerLinearEmbedding_mk] at he
  apply (Submodule.Quotient.eq _).mp
  change (power (ZMod 2) G (n+1)).mkQ (delta (ZMod 2) (g : G)-1) =
    (power (ZMod 2) G (n+1)).mkQ (initialDifference G n g)
  rw [initialDifference, map_sum]
  simp only [map_smul]
  exact he.symm

theorem initialDifference_mem (g : dimensionSubgroup (ZMod 2) G n) :
    initialDifference G n g ∈ power (ZMod 2) G n := by
  apply Submodule.sum_mem
  intro i _
  exact (power (ZMod 2) G n).smul_mem _ (layerBasisLift G n i).property

variable (m : ℕ) [hm : Fact (1 ≤ m)]

omit hn hm in
/-- Commuting two group differences has a linear homogeneous initial form
in exactly the sum of their degrees. The quotient layer and coefficients
are those already independently constructed. -/
theorem commutator_initial_form
    [Fact (1 ≤ m+n)] (g : dimensionSubgroup (ZMod 2) G m)
    (h : dimensionSubgroup (ZMod 2) G n) :
    (delta (ZMod 2) (g : G)-1)*(delta (ZMod 2) (h : G)-1) -
      (delta (ZMod 2) (h : G)-1)*(delta (ZMod 2) (g : G)-1) -
      initialDifference G (m+n) ⟨(g : G)*(h : G)*(g : G)⁻¹*(h : G)⁻¹,
        commutator_mem (ZMod 2) G g.property h.property⟩ ∈ power (ZMod 2) G (m+n+1) := by
  let c : dimensionSubgroup (ZMod 2) G (m+n) :=
    ⟨(g : G)*(h : G)*(g : G)⁻¹*(h : G)⁻¹,
      commutator_mem (ZMod 2) G g.property h.property⟩
  have hc : delta (ZMod 2) (c : G) * delta (ZMod 2) ((h : G)*(g : G)) =
      delta (ZMod 2) (g : G) * delta (ZMod 2) (h : G) := by
    simp only [delta_mul]
    congr 1
    dsimp [c]
    group
  have he : (delta (ZMod 2) (g : G)-1)*(delta (ZMod 2) (h : G)-1) -
      (delta (ZMod 2) (h : G)-1)*(delta (ZMod 2) (g : G)-1) -
      (delta (ZMod 2) (c : G)-1) =
      (delta (ZMod 2) (c : G)-1) * (delta (ZMod 2) ((h : G)*(g : G))-1) := by
    conv_rhs => rw [mul_sub, sub_mul, hc, ← delta_mul]
    noncomm_ring
  have herror := mul_mem_succ (ZMod 2) G c.property
    (by simp : augmentation (ZMod 2) G (delta (ZMod 2) ((h : G)*(g : G))-1) = 0)
  rw [← he] at herror
  have hrem := difference_sub_initial_mem G (m+n) c
  have ht := (power (ZMod 2) G (m+n+1)).add_mem herror hrem
  simpa only [sub_add_sub_cancel] using ht

omit hn in
/-- Squaring a group difference in characteristic two has a linear
homogeneous initial form at twice its degree. -/
theorem square_initial_form [Fact (1 ≤ 2*n)]
    (g : dimensionSubgroup (ZMod 2) G n) :
    (delta (ZMod 2) (g : G)-1)*(delta (ZMod 2) (g : G)-1) -
      initialDifference G (2*n) ⟨(g : G)^2, square_mem (ZMod 2) G g.property⟩ ∈
        power (ZMod 2) G (2*n+1) := by
  have hs : delta (ZMod 2) (g : G) + delta (ZMod 2) (g : G) = 0 := by
    ext x
    simp [CharTwo.add_self_eq_zero]
  have hn1 : -(1 : A (ZMod 2) G) = 1 := by
    ext x
    simp [CharTwo.neg_eq]
  have hid : (delta (ZMod 2) (g : G)-1)*(delta (ZMod 2) (g : G)-1) =
      delta (ZMod 2) ((g : G)^2)-1 := by
    calc
      _ = delta (ZMod 2) (g : G)*delta (ZMod 2) (g : G) -
          (delta (ZMod 2) (g : G)+delta (ZMod 2) (g : G)) + 1 := by noncomm_ring
      _ = _ := by simp [hs, sub_eq_add_neg, hn1, pow_two]
  rw [hid]
  exact difference_sub_initial_mem G (2*n)
    ⟨(g : G)^2, square_mem (ZMod 2) G g.property⟩

end UnitDistance.GroupAugmentation
