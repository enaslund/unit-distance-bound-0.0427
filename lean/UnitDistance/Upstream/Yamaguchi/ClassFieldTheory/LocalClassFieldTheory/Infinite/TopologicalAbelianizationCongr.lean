/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Functoriality of topological abelianization under equivalence

A continuous multiplicative equivalence carries the closure of the
commutator subgroup onto the corresponding closure.  It therefore descends
to a continuous multiplicative equivalence of topological abelianizations.
-/

noncomputable section

namespace LocalClassFieldTheory

universe u v

variable {G : Type u} {H : Type v}
  [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

private theorem topologicalCommutatorClosure_le_comap
    (e : G ≃ₜ* H) :
    (commutator G).topologicalClosure ≤
      (commutator H).topologicalClosure.comap
        e.toMulEquiv.toMonoidHom := by
  apply Subgroup.topologicalClosure_minimal
  · intro x hx
    change e x ∈ (commutator H).topologicalClosure
    apply Subgroup.le_topologicalClosure
    have hmap :
        (commutator G).map e.toMulEquiv.toMonoidHom =
          commutator H := by
      rw [map_commutator_eq]
      have hrange : e.toMulEquiv.toMonoidHom.range = ⊤ :=
        MonoidHom.range_eq_top.mpr e.surjective
      rw [hrange]
      rfl
    rw [← hmap]
    exact Subgroup.mem_map_of_mem e.toMulEquiv.toMonoidHom hx
  · exact (Subgroup.isClosed_topologicalClosure _).preimage e.continuous

private def topologicalAbelianizationMap (e : G ≃ₜ* H) :
    TopologicalAbelianization G →* TopologicalAbelianization H :=
  QuotientGroup.map
    (commutator G).topologicalClosure
    (commutator H).topologicalClosure
    e.toMulEquiv.toMonoidHom
    (topologicalCommutatorClosure_le_comap e)

@[simp]
private theorem topologicalAbelianizationMap_mk
    (e : G ≃ₜ* H) (x : G) :
    topologicalAbelianizationMap e (QuotientGroup.mk x) =
      QuotientGroup.mk (e x) :=
  rfl

private theorem topologicalAbelianizationMap_continuous
    (e : G ≃ₜ* H) :
    Continuous (topologicalAbelianizationMap e) := by
  apply (QuotientGroup.isQuotientMap_mk
    (commutator G).topologicalClosure).continuous_iff.2
  change Continuous (QuotientGroup.mk ∘ e.toHomeomorph)
  exact QuotientGroup.continuous_mk.comp e.continuous

private def topologicalAbelianizationMulEquiv (e : G ≃ₜ* H) :
    TopologicalAbelianization G ≃* TopologicalAbelianization H where
  toFun := topologicalAbelianizationMap e
  invFun := topologicalAbelianizationMap e.symm
  left_inv q := by
    refine q.inductionOn' ?_
    intro x
    simp
  right_inv q := by
    refine q.inductionOn' ?_
    intro x
    simp
  map_mul' x y := map_mul (topologicalAbelianizationMap e) x y

/-- A continuous multiplicative equivalence induces the canonical
continuous multiplicative equivalence of topological abelianizations. -/
noncomputable def topologicalAbelianizationCongr (e : G ≃ₜ* H) :
    TopologicalAbelianization G ≃ₜ* TopologicalAbelianization H :=
  { topologicalAbelianizationMulEquiv e with
    continuous_toFun := topologicalAbelianizationMap_continuous e
    continuous_invFun := topologicalAbelianizationMap_continuous e.symm }

/-- States the theorem `topologicalAbelianizationCongr_mk`. -/
@[simp]
theorem topologicalAbelianizationCongr_mk
    (e : G ≃ₜ* H) (x : G) :
    topologicalAbelianizationCongr e (QuotientGroup.mk x) =
      QuotientGroup.mk (e x) :=
  rfl

end LocalClassFieldTheory
