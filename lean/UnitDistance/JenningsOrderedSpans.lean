module

public import UnitDistance.JenningsHomogeneousRelations

@[expose] public section
set_option backward.privateInPublic true


/-!
# Identification of ordered-list spans with weighted binary monomial spans

The correspondence keeps the actual original order and actual total weight.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.JenningsCollection

variable {ι M : Type*} [Monoid M]

theorem filter_map_prod (l : List ι) (p : ι → Bool) (f : ι → M) :
    ((l.filter p).map f).prod = (l.map (fun i => if p i then f i else 1)).prod := by
  induction l with
  | nil => simp
  | cons i l ih => cases hi : p i <;> simp [hi,ih]

theorem filter_map_sum (l : List ι) (p : ι → Bool) (w : ι → ℕ) :
    ((l.filter p).map w).sum = (l.map (fun i => if p i then w i else 0)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => cases hi : p i <;> simp [hi,ih]

/-- Strictly increasing positional lists are exactly the selected positions. -/
theorem increasing_eq_filter_finRange {r : ℕ} (l : List (Fin r))
    (hl : l.Pairwise (· < ·)) :
    l = (List.finRange r).filter (fun i => decide (i ∈ l)) := by
  apply List.SortedLT.eq_of_mem_iff hl.sortedLT
    ((List.sortedLT_finRange r).pairwise.filter _).sortedLT
  intro i
  simp

end UnitDistance.JenningsCollection

namespace UnitDistance.GroupAugmentation
variable (G : Type*) [Group G] [Finite G] (hG : IsPGroup 2 G)
open JenningsCollection

/-- Actual ordered-list monomials give precisely the weighted binary span. -/
theorem orderedSpan_eq_weightedMonomialSpan (n : ℕ) :
    orderedSpan (ZMod 2) G (Fin (homogeneousDifferences G).length)
      (fun i => (homogeneousDifferences G).get i)
      (fun i => groupDegree G hG (monomialLetter G i)) n = weightedMonomialSpan G hG n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro a ⟨l,hl,hw,rfl⟩
    let c : Fin (homogeneousDifferences G).length → Bool := fun i => decide (i ∈ l)
    have he := increasing_eq_filter_finRange l hl
    have hv : wordValue (ZMod 2) G _ (fun i => (homogeneousDifferences G).get i) l =
        augmentationMonomial G c := by
      change (l.map _).prod = (List.ofFn _).prod
      rw [he,filter_map_prod,← List.ofFn_eq_map]
    have hd : wordDegree _ (fun i => groupDegree G hG (monomialLetter G i)) l =
        monomialWeight G hG c := by
      change (l.map _).sum = ∑ i, _
      rw [he,filter_map_sum,← List.ofFn_eq_map,List.sum_ofFn]
    exact Submodule.subset_span ⟨c, hd ▸ hw, hv⟩
  · apply Submodule.span_le.mpr
    rintro a ⟨c,hc,rfl⟩
    let l := (List.finRange (homogeneousDifferences G).length).filter c
    have hv : augmentationMonomial G c =
        wordValue (ZMod 2) G _ (fun i => (homogeneousDifferences G).get i) l := by
      change (List.ofFn _).prod = (((List.finRange (homogeneousDifferences G).length).filter c).map _).prod
      rw [filter_map_prod,← List.ofFn_eq_map]
    have hd : monomialWeight G hG c =
        wordDegree _ (fun i => groupDegree G hG (monomialLetter G i)) l := by
      change (∑ i, _) = (((List.finRange (homogeneousDifferences G).length).filter c).map _).sum
      rw [filter_map_sum,← List.ofFn_eq_map,List.sum_ofFn]
    exact Submodule.subset_span ⟨l,(List.sortedLT_finRange _).pairwise.filter _,hd ▸ hc,hv⟩

/-- The degree-zero ordered span fills the actual algebra. -/
theorem orderedSpan_zero_eq_top :
    orderedSpan (ZMod 2) G (Fin (homogeneousDifferences G).length)
      (fun i => (homogeneousDifferences G).get i)
      (fun i => groupDegree G hG (monomialLetter G i)) 0 = ⊤ := by
  rw [orderedSpan_eq_weightedMonomialSpan]
  have hs : {a | ∃ c, 0 ≤ monomialWeight G hG c ∧ a = augmentationMonomial G c} =
      Set.range (augmentationMonomial G) := by
    ext a
    simp only [Nat.zero_le, true_and, Set.mem_setOf_eq, Set.mem_range]
    exact exists_congr (fun _ => eq_comm)
  rw [weightedMonomialSpan,hs,span_augmentationMonomial G hG]

end UnitDistance.GroupAugmentation
