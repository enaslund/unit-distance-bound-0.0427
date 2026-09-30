/-
Copyright (c) 2026 The Erdős unit-distance formalization contributors.
Released under Apache 2.0 license as described in third-party/erdos-unit-distance/LICENSE.

Selected proof adaptation from logical-intelligence/erdos-unit-distance,
commit b6493074dd103ca32ea4f5e9b0bc9cb3a0379f2e,
ErdosUnitDistance/Internal/ClassFieldTheory/Witness.lean.
Local modifications: namespace/import port, separation from arithmetic
maximal-extension assumptions, and explicit actual-field family packaging.
See third-party/erdos-unit-distance/README.md for scope and provenance.
-/
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Order

@[expose] public section
set_option backward.privateInPublic true


/-!
# Growing finite quotients of an actual infinite profinite group

The construction separates successively more actual distinct group elements
by open normal subgroups and takes successive intersections. No arithmetic
maximal-extension or splitting assumption is used.

Adapted from `ErdosUnitDistance/Internal/ClassFieldTheory/Witness.lean`,
`openNormalChain`; provenance is recorded in
`third-party/erdos-unit-distance/README.md`.
-/

noncomputable section
namespace UnitDistance.ProfiniteQuotient
theorem openNormalChain (Q0 : Type*) [Group Q0] [TopologicalSpace Q0] [IsTopologicalGroup Q0] [T2Space Q0] [CompactSpace Q0] [TotallyDisconnectedSpace Q0] [Infinite Q0] : ∃ U : ℕ → OpenNormalSubgroup Q0, ((U 0 : Subgroup Q0) = ⊤) ∧ (∀ j, U (j + 1) ≤ U j) ∧ Filter.Tendsto (fun j => Nat.card (Q0 ⧸ (U j).toSubgroup)) Filter.atTop Filter.atTop := by
  classical
  let e : ℕ ↪ Q0 := Infinite.natEmbedding Q0
  let bad : ℕ → Finset Q0 := fun n =>
    ((((Finset.univ : Finset (Fin (n + 1))).product Finset.univ).filter
      (fun p : Fin (n + 1) × Fin (n + 1) => p.1 ≠ p.2)).image
      (fun p => (e p.1)⁻¹ * e p.2))
  have hbad_one : ∀ n, (1 : Q0) ∉ bad n := by
    intro n h1
    rcases Finset.mem_image.mp h1 with ⟨p, hp, hp1⟩
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have heq : e p.1 = e p.2 := by
      exact inv_mul_eq_one.mp hp1
    exact hpne (Fin.ext (e.injective heq))
  let H : ℕ → OpenNormalSubgroup Q0 := fun n =>
    Classical.choose <|
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (U := (bad n : Set Q0)ᶜ)
        ((bad n).isClosed.isOpen_compl)
        (by
          change (1 : Q0) ∉ bad n
          exact hbad_one n)
  have hHsub : ∀ n, ((H n : Set Q0) ⊆ (bad n : Set Q0)ᶜ) := by
    intro n
    exact Classical.choose_spec <|
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (U := (bad n : Set Q0)ᶜ)
        ((bad n).isClosed.isOpen_compl)
        (by
          change (1 : Q0) ∉ bad n
          exact hbad_one n)
  let topON : OpenNormalSubgroup Q0 :=
    { toOpenSubgroup := ⊤
      isNormal' := Subgroup.normal_top }
  let U : ℕ → OpenNormalSubgroup Q0 := Nat.rec topON (fun n Un => Un ⊓ H n)
  have hsize : ∀ n, n + 1 ≤ Nat.card (Q0 ⧸ (U (n + 1)).toSubgroup) := by
    intro n
    let f : Fin (n + 1) → Q0 ⧸ (U (n + 1)).toSubgroup := fun i => QuotientGroup.mk (e i)
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      have hmemU : (e i)⁻¹ * e j ∈ (U (n + 1) : Subgroup Q0) := by
        exact QuotientGroup.eq.mp hij
      have hmemH : (e i)⁻¹ * e j ∈ (H n : Subgroup Q0) := by
        have hle : U (n + 1) ≤ H n := by
          change Nat.rec topON (fun n Un => Un ⊓ H n) n ⊓ H n ≤ H n
          exact inf_le_right
        exact hle hmemU
      have hnotbad : (e i)⁻¹ * e j ∉ bad n := by
        simpa using hHsub n hmemH
      have hbadmem : (e i)⁻¹ * e j ∈ bad n := by
        apply Finset.mem_image.mpr
        refine ⟨(i, j), ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨by simp, hne⟩
      exact hnotbad hbadmem
    simpa [f, Nat.card_fin] using (Nat.card_le_card_of_injective f hf)
  have hbound : ∀ j, j ≤ Nat.card (Q0 ⧸ (U j).toSubgroup) := by
    intro j
    cases j with
    | zero => exact Nat.zero_le _
    | succ n => exact hsize n
  refine ⟨U, ?_, ?_, ?_⟩
  · change (topON : Subgroup Q0) = ⊤
    rfl
  · intro j
    cases j with
    | zero =>
        change topON ⊓ H 0 ≤ topON
        exact inf_le_left
    | succ n =>
        change (Nat.rec topON (fun n Un => Un ⊓ H n) (n + 1) ⊓ H (n + 1)) ≤
          Nat.rec topON (fun n Un => Un ⊓ H n) (n + 1)
        exact inf_le_left
  · rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro a ha
    exact le_trans ha (hbound a)

end UnitDistance.ProfiniteQuotient
