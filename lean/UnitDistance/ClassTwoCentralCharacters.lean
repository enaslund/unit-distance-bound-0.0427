module

public import UnitDistance.GroupAugmentationClassTwo
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

@[expose] public section
set_option backward.privateInPublic true


/-!
# Continuous characters detected by a bilinear class-two quotient

An actual continuous map into a finite discrete class-two model supplies
continuous, ambient-conjugation-invariant characters on any subgroup mapping
to the central coordinates. All evaluations are the literal linear
coordinates of the image; no character existence is assumed.
-/

noncomputable section

namespace UnitDistance.ClassTwo

variable {k V W G : Type*} [CommRing k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (β : V →ₗ[k] V →ₗ[k] W)

namespace GroupModel

/-- Conjugating an element with zero base leaves its actual central
coordinates unchanged. -/
theorem conjugate_of_base_zero (g r : GroupModel β) (hr : r.base = 0) :
    g * r * g⁻¹ = r := by
  ext <;> simp only [mul_base, mul_central, inv_base, inv_central, hr,
    add_zero, map_zero, map_neg] <;> abel

end GroupModel

variable [TopologicalSpace (GroupModel β)] [DiscreteTopology (GroupModel β)]
  [TopologicalSpace k]

/-- A linear central coordinate pulled back along an actual continuous
homomorphism. The zero-base condition proves multiplicativity. -/
def centralCharacter
    (q : G →ₜ* GroupModel β) (S : Subgroup G)
    (hbase : ∀ r : S, (q r).base = 0) (ℓ : W →ₗ[k] k) :
    S →ₜ* Multiplicative k where
  toFun r := Multiplicative.ofAdd (ℓ (q r).central)
  map_one' := by
    change Multiplicative.ofAdd (ℓ (q 1).central) = 1
    rw [map_one, GroupModel.one_central, map_zero]
    rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    change ℓ (q (a.1 * b.1)).central = ℓ (q a).central + ℓ (q b).central
    rw [map_mul, GroupModel.mul_central, hbase a, map_zero, LinearMap.zero_apply,
      add_zero, map_add]
  continuous_toFun :=
    (continuous_of_discreteTopology :
      Continuous (fun x : GroupModel β ↦ Multiplicative.ofAdd (ℓ x.central))).comp
        (q.continuous_toFun.comp continuous_subtype_val)

@[simp] theorem centralCharacter_apply
    (q : G →ₜ* GroupModel β) (S : Subgroup G)
    (hbase : ∀ r : S, (q r).base = 0) (ℓ : W →ₗ[k] k) (r : S) :
    (centralCharacter β q S hbase ℓ r).toAdd = ℓ (q r).central := rfl

/-- These characters are invariant under the actual ambient conjugation
action on a normal subgroup. -/
theorem centralCharacter_conjNormal
    (q : G →ₜ* GroupModel β) (S : Subgroup G) [S.Normal]
    (hbase : ∀ r : S, (q r).base = 0) (ℓ : W →ₗ[k] k) (g : G) (r : S) :
    centralCharacter β q S hbase ℓ (MulAut.conjNormal g r) =
      centralCharacter β q S hbase ℓ r := by
  apply Multiplicative.toAdd.injective
  change ℓ (q (g * r.1 * g⁻¹)).central = ℓ (q r).central
  rw [map_mul, map_mul, map_inv, GroupModel.conjugate_of_base_zero β (q g) (q r)
    (hbase r)]

end UnitDistance.ClassTwo
