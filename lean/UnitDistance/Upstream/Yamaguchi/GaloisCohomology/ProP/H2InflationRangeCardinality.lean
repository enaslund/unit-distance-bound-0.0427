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

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2InflationRangeBound
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Module.Pi

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false
/-!
# Cardinality bounds on finite-stage degree-two inflation

A uniform bound p^d on finite-stage inflation images gives finite
continuous H² of dimension at most d. Finiteness of the finite-stage
cohomology and its image is constructed, rather than assumed.
-/

open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC

noncomputable section
universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- A uniform cardinality bound for finite-stage images bounds the full
continuous degree-two cohomology dimension. -/
theorem finiteDimensional_and_finrank_degree_two_le_of_inflationRange_natCard
    (d : ℕ)
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    (hcard : ∀ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G,
      Nat.card (degreeTwoInflationRange (p := p) U) ≤ p ^ d) :
      FiniteDimensional (ZMod p) (continuousCohomologyZModPLifted p G 2) ∧
      Module.finrank (ZMod p) (continuousCohomologyZModPLifted p G 2) ≤ d := by
  letI : AddCommGroup (Fin d → ZMod p) :=
    { Pi.addCommGroup with toAddCommMonoid := Pi.addCommMonoid }
  letI : Module (ZMod p) (Fin d → ZMod p) := {
    smul := fun r f i => r * f i
    one_smul := by intro f; ext i; simp
    mul_smul := by intro r s f; ext i; simp [mul_assoc]
    smul_add := by intro r f g; ext i; simp [mul_add]
    smul_zero := by intro r; ext i; simp
    add_smul := by intro r s f; ext i; simp [add_mul]
    zero_smul := by intro f; ext i; simp }
  letI : FiniteDimensional (ZMod p) (Fin d → ZMod p) := inferInstance
  have h := finiteDimensional_and_finrank_degree_two_le_of_inflationRange_embeddings
    (p := p) (G := G) (W := Fin d → ZMod p) hG (by
      intro U
      let Q := G ⧸ (U.1 : Subgroup G)
      let : FiniteDimensional (ZMod p) (continuousCohomologyZModPLifted p Q 2) :=
        finiteDimensional_degree_two_of_finite (p := p) (Q := Q) inferInstance
      let : FiniteDimensional (ZMod p) (degreeTwoInflationRange (p := p) U) :=
        LinearMap.finiteDimensional_range _
      have hc : p ^ Module.finrank (ZMod p) (degreeTwoInflationRange (p := p) U) ≤
          p ^ d := by
        have he : Nat.card (degreeTwoInflationRange (p := p) U) =
            p ^ Module.finrank (ZMod p) (degreeTwoInflationRange (p := p) U) := by
          simpa only [Nat.card_zmod] using
            (Module.natCard_eq_pow_finrank (K := ZMod p)
              (V := degreeTwoInflationRange (p := p) U))
        exact he ▸ hcard U
      have hd : Module.finrank (ZMod p) (degreeTwoInflationRange (p := p) U) ≤ d :=
        (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hc
      apply finrank_le_iff_exists_linearMap.mp
      simpa only [Module.finrank_pi, Fintype.card_fin] using hd)
  simpa using h

end
end ClassFieldTower.Cohomology
