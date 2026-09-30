module

public import UnitDistance.GeometryFinite
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Data.ENNReal.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Uniform finite truncation of the logarithmic lattice

A compact enclosure of the fundamental domain and finitely many compact
profile supports imply one finite lattice cutoff valid for all reference
labels and all parameters in that domain. No numerical tail truncation or
coordinate decomposition of the lattice is used.
-/

open scoped Classical ENNReal

namespace UnitDistance

theorem finite_log_overlap_support {H I J : Type*} [AddCommGroup H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [Fintype I] [Fintype J]
    (L : AddSubgroup H) [DiscreteTopology L] (hL : IsClosed (L : Set H))
    (Q Qbar : Set H) (hQ : Q ⊆ Qbar) (hQbar : IsCompact Qbar)
    (K : J → Set H) (hK : ∀ j, IsCompact (K j))
    (Φ : J → H → ℝ≥0∞) (hΦ : ∀ j, Function.support (Φ j) ⊆ K j)
    (shift : I → J → H) :
    ∃ cutoff : Finset L, ∀ i j h, h ∈ Q → ∀ l ∉ cutoff,
      Φ j (shift i j - ((l : H) + h)) = 0 := by
  classical
  have hfinite (i : I) (j : J) :
      {l : L | ∃ h ∈ Q, Φ j (shift i j - ((l : H) + h)) ≠ 0}.Finite := by
    let R := (fun hs : H × H => shift i j - hs.1 - hs.2) '' (Qbar ×ˢ K j)
    have hR : IsCompact R := (hQbar.prod (hK j)).image
      ((continuous_const.sub continuous_fst).sub continuous_snd)
    apply (finite_lattice_window L hL R hR 0).subset
    rintro l ⟨h, hh, hl⟩
    change (l : H) + 0 ∈ R
    rw [add_zero]
    refine ⟨(h, shift i j - ((l : H) + h)), ⟨hQ hh, hΦ j hl⟩, ?_⟩
    dsimp
    abel
  let cutoff : Finset L := Finset.univ.biUnion (fun i : I =>
    Finset.univ.biUnion (fun j : J => (hfinite i j).toFinset))
  refine ⟨cutoff, ?_⟩
  intro i j h hh l hl
  by_contra hne
  apply hl
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨j, Finset.mem_univ _, ?_⟩
  exact (hfinite i j).mem_toFinset.mpr ⟨h, hh, hne⟩

/-- The support hypothesis can be supplied by compact support of each
ordinary overlap profile. A half-open fundamental domain may use its compact
closure as `Qbar`; it need not itself be closed. -/
theorem finite_log_cutoff_of_compactSupport {H I J : Type*} [AddCommGroup H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [Fintype I] [Fintype J]
    (L : AddSubgroup H) [DiscreteTopology L] (hL : IsClosed (L : Set H))
    (Q Qbar : Set H) (hQ : Q ⊆ Qbar) (hQbar : IsCompact Qbar)
    (Φ : J → H → ℝ≥0∞) (hΦ : ∀ j, HasCompactSupport (Φ j))
    (shift : I → J → H) :
    ∃ cutoff : Finset L, ∀ i j h, h ∈ Q → ∀ l ∉ cutoff,
      Φ j (shift i j - ((l : H) + h)) = 0 :=
  finite_log_overlap_support L hL Q Qbar hQ hQbar
    (fun j => tsupport (Φ j)) hΦ Φ (fun j => subset_tsupport (Φ j)) shift

end UnitDistance
