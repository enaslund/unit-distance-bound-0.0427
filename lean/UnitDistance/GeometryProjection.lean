module

public import UnitDistance.Target

@[expose] public section
set_option backward.privateInPublic true


/-!
# Faithful extraction of planar unit distances

Distinguished edges are actual ordered pairs of elements of a finite set,
with a prescribed difference. A compact complex embedding sends norm-one
field differences to ordinary Euclidean unit vectors. No multiplicities
are introduced by projection.
-/

open scoped Classical

namespace UnitDistance

/-- Ordered edges inherited from a finite set of allowed displacements. -/
noncomputable def displacementPairs {K : Type*} [AddGroup K]
    (V D : Finset K) : Finset (K × K) :=
  (V ×ˢ V).filter (fun e => e.2 - e.1 ∈ D)

@[simp] theorem displacementPairs_empty {K : Type*} [AddGroup K] (D : Finset K) :
    displacementPairs ∅ D = ∅ := by simp [displacementPairs]

/-- Inherited ordered edges are a subset of all ordered vertex pairs. -/
theorem displacementPairs_card_bound {K : Type*} [AddGroup K] (V D : Finset K) :
    (displacementPairs V D).card ≤ V.card * V.card := by
  calc
    (displacementPairs V D).card ≤ (V ×ˢ V).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = V.card * V.card := Finset.card_product _ _

/-- An injective coordinate projection preserves vertices and injects every
inherited ordered edge into the ordinary planar unit-distance graph. -/
theorem displacementPairs_card_le {K : Type*} [AddGroup K]
    (V D : Finset K) (φ : K → ℂ) (hφ : Function.Injective φ)
    (hunit : ∀ x ∈ V, ∀ y ∈ V, y - x ∈ D → dist (φ x) (φ y) = 1) :
    (displacementPairs V D).card ≤ (orderedUnitPairs (V.image φ)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun e : K × K => (φ e.1, φ e.2))
  · intro e he
    obtain ⟨heV, heD⟩ := Finset.mem_filter.mp he
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp heV
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image_of_mem φ hx,
      Finset.mem_image_of_mem φ hy⟩, hunit e.1 hx e.2 hy heD⟩
  · intro e he f hf hef
    exact Prod.ext (hφ (congrArg Prod.fst hef)) (hφ (congrArg Prod.snd hef))

/-- Exact unordered-edge factor and exact preservation of cardinality. -/
theorem project_displacement_graph {K : Type*} [AddGroup K]
    (V D : Finset K) (φ : K → ℂ) (hφ : Function.Injective φ)
    (hunit : ∀ x ∈ V, ∀ y ∈ V, y - x ∈ D → dist (φ x) (φ y) = 1) :
    ∃ U : Finset ℂ, U.card = V.card ∧
      ((displacementPairs V D).card : ℝ) / 2 ≤ unitPairs U := by
  refine ⟨V.image φ, Finset.card_image_of_injective V hφ, ?_⟩
  unfold unitPairs
  exact div_le_div_of_nonneg_right (by exact_mod_cast displacementPairs_card_le V D φ hφ hunit)
    (by norm_num)

/-- At a compact place, an element with relative norm one has complex norm
one. The involution may be any ring hom satisfying the stated compatibility. -/
theorem complex_norm_of_relative_norm_one {K : Type*} [CommRing K]
    (φ : K →+* ℂ) (ι : K →+* K)
    (hcompact : ∀ x, φ (ι x) = star (φ x))
    (β : K) (hβ : β * ι β = 1) : ‖φ β‖ = 1 := by
  have h : φ β * star (φ β) = 1 := by
    simpa only [map_mul, map_one, hcompact] using congrArg φ hβ
  have hn := congrArg norm h
  simp only [norm_mul, norm_star, norm_one] at hn
  have hnonneg := norm_nonneg (φ β)
  nlinarith

/-- Projection through an actual field embedding, including an arbitrary
common planar translate. Its hypotheses concern relative norms and the
embedding, not any graph count. -/
theorem project_field_displacements {K : Type*} [Field K]
    (V D : Finset K) (φ : K →+* ℂ) (ι : K →+* K)
    (hcompact : ∀ x, φ (ι x) = star (φ x))
    (hD : ∀ β ∈ D, β * ι β = 1) (z : ℂ) :
    ∃ U : Finset ℂ, U.card = V.card ∧
      ((displacementPairs V D).card : ℝ) / 2 ≤ unitPairs U := by
  apply project_displacement_graph V D (fun x => φ x + z)
  · intro x y hxy
    exact φ.injective (add_right_cancel hxy)
  · intro x hx y hy hxy
    rw [dist_add_right, dist_eq_norm, norm_sub_rev, ← map_sub]
    exact complex_norm_of_relative_norm_one φ ι hcompact (y - x) (hD _ hxy)

end UnitDistance
