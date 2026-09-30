module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Compactness.Compact

@[expose] public section
set_option backward.privateInPublic true


/-!
# Simultaneous tame pairs in a profinite group

Compactness turns separately chosen finite-quotient witnesses into an actual pair.
No compatibility between the finite witnesses is assumed.
-/

namespace UnitDistance
namespace ProfiniteTame

open Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The open normal subgroups of a profinite group separate the identity. -/
theorem eq_one_of_mem_all_openNormal {g : G}
    (hg : ∀ U : OpenNormalSubgroup G, g ∈ U) : g = 1 := by
  by_contra h
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := G) (isClosed_singleton (x := g)).isOpen_compl (by simpa using Ne.symm h)
  have := hU (hg U)
  simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false] at this

/-- A continuous equation with fixed closed labels can be solved in a compact space
if it can be solved modulo every open normal subgroup. -/
theorem exists_labeled_eq_one {X A : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace A] [T2Space A] (f : X → G) (hf : Continuous f)
    (c : X → A) (hc : Continuous c) (a : A)
    (h : ∀ U : OpenNormalSubgroup G, ∃ x, c x = a ∧ f x ∈ U) :
    ∃ x, c x = a ∧ f x = 1 := by
  let C : OpenNormalSubgroup G → Set X := fun U => {x | c x = a ∧ f x ∈ U}
  have hclosed (U : OpenNormalSubgroup G) : IsClosed (C U) :=
    (isClosed_eq hc continuous_const).inter (U.toOpenSubgroup.isClosed.preimage hf)
  have hdir : Directed (· ⊇ ·) C := by
    intro U V
    refine ⟨U ⊓ V, ?_, ?_⟩
    · intro x hx
      exact ⟨hx.1, hx.2.1⟩
    · intro x hx
      exact ⟨hx.1, hx.2.2⟩
  letI : Nonempty (OpenNormalSubgroup G) :=
    ⟨{ toOpenSubgroup := ⊤, isNormal' := show (⊤ : Subgroup G).Normal from inferInstance }⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C
    hdir (fun U => h U) (fun U => (hclosed U).isCompact) hclosed
  have hx' (U : OpenNormalSubgroup G) : c x = a ∧ f x ∈ U :=
    mem_iInter.mp hx U
  exact ⟨x, (hx' Classical.ofNonempty).1,
    eq_one_of_mem_all_openNormal (fun U => (hx' U).2)⟩

/-- Prescribed finite labels and tame relations in every finite quotient produce an
actual tame pair. Finiteness of the label group is unnecessary: Hausdorff suffices. -/
theorem exists_tame_pair {A : Type*} [Group A] [TopologicalSpace A] [T2Space A]
    (χ : G →ₜ* A) (a b : A) (q : ℕ)
    (h : ∀ U : OpenNormalSubgroup G, ∃ τ φ : G,
      χ τ = a ∧ χ φ = b ∧ φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ U) :
    ∃ τ φ : G, χ τ = a ∧ χ φ = b ∧ φ * τ * φ⁻¹ = τ ^ q := by
  let f : G × G → G := fun x => x.2 * x.1 * x.2⁻¹ * (x.1 ^ q)⁻¹
  have hf : Continuous f := by fun_prop
  let c : G × G → A × A := fun x => (χ x.1, χ x.2)
  have hc : Continuous c := by fun_prop
  obtain ⟨x, hx, heq⟩ := exists_labeled_eq_one f hf c hc (a, b) (by
    intro U
    obtain ⟨τ, φ, hτ, hφ, hrel⟩ := h U
    exact ⟨(τ, φ), Prod.ext hτ hφ, hrel⟩)
  refine ⟨x.1, x.2, congrArg Prod.fst hx, congrArg Prod.snd hx, ?_⟩
  exact mul_inv_eq_one.mp heq

/-- The same compactness theorem with the residual word written using integer powers. -/
theorem exists_tame_pair_of_zpow {A : Type*} [Group A] [TopologicalSpace A] [T2Space A]
    (χ : G →ₜ* A) (a b : A) (q : ℕ)
    (h : ∀ U : OpenNormalSubgroup G, ∃ τ φ : G,
      χ τ = a ∧ χ φ = b ∧ φ * τ * φ⁻¹ * τ ^ (-(q : ℤ)) ∈ U) :
    ∃ τ φ : G, χ τ = a ∧ χ φ = b ∧ φ * τ * φ⁻¹ = τ ^ q := by
  apply exists_tame_pair χ a b q
  simpa only [zpow_neg, zpow_natCast] using h

end ProfiniteTame
end UnitDistance
