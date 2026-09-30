module

public import UnitDistance.JenningsOrderedSpans
public import UnitDistance.JenningsFilteredSpanning

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact weighted augmentation basis theorem for every finite 2-group

The ordinary monomial basis, actual homogeneous weights, collection
relations, group generation, and augmentation nilpotence are all proved
from the actual finite group. No Jennings/PBW hypothesis is used.
-/

noncomputable section
namespace UnitDistance.Jennings
variable {G : Type*} [Group G]

/-- Every ordered binary group word lies in the subgroup containing its letters. -/
theorem binaryWords_subset_subgroup (l : List G) (H : Subgroup G)
    (hl : ∀ g ∈ l, g ∈ H) : binaryWords l ⊆ H := by
  induction l with
  | nil => simp
  | cons g l ih =>
    rintro z ⟨a,ha,b,hb,rfl⟩
    apply H.mul_mem
    · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
      rcases ha with ha | ha
      · rw [ha]; exact H.one_mem
      · rw [ha]; exact hl g List.mem_cons_self
    · exact ih (fun h hh => hl h (List.mem_cons_of_mem _ hh)) hb

end UnitDistance.Jennings

namespace UnitDistance.GroupAugmentation
variable (G : Type*) [Group G] [Finite G] (hG : IsPGroup 2 G)

include hG in
/-- The actual homogeneous positional letters generate the actual group. -/
theorem monomialLetter_generates : Subgroup.closure (Set.range (monomialLetter G)) = ⊤ := by
  apply eq_top_iff.mpr
  intro g _
  have hg : g ∈ Jennings.binaryWords (homogeneousGenerators G) := by
    rw [binaryWords_homogeneousGenerators G hG]
    trivial
  apply Jennings.binaryWords_subset_subgroup (homogeneousGenerators G)
    (Subgroup.closure (Set.range (monomialLetter G))) ?_ hg
  intro a ha
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
  let j : Fin (homogeneousDifferences G).length :=
    ⟨i.val, by simp [homogeneousDifferences]⟩
  apply Subgroup.subset_closure
  exact ⟨j,hi⟩

/-- The exact weighted Jennings augmentation filtration for every finite
2-group, using the actual constructed homogeneous monomial basis. -/
theorem weightedMonomialSpan_eq_power (n : ℕ) :
    weightedMonomialSpan G hG n = power (ZMod 2) G n := by
  rw [← orderedSpan_eq_weightedMonomialSpan]
  apply JenningsCollection.orderedSpan_eq_power (ZMod 2) G
    (Fin (homogeneousDifferences G).length)
    (fun i => (homogeneousDifferences G).get i)
    (fun i => groupDegree G hG (monomialLetter G i)) (monomialLetter G)
    (monomialLetter_generates G hG) (get_homogeneousDifferences G)
    (fun i => ?_) (monomialLetter_degree_pos G hG)
    (orderedSpan_zero_eq_top G hG) (homogeneousRelations G hG)
    (Nat.card G) (power_card_eq_bot G 2 hG) n
  rw [get_homogeneousDifferences]
  exact mem_dimensionSubgroup_groupDegree G hG _

/-- The reverse inclusion is derived from actual collection and actual
nilpotence, completing the previously proved forward inclusion. -/
theorem power_le_weightedMonomialSpan (n : ℕ) :
    power (ZMod 2) G n ≤ weightedMonomialSpan G hG n :=
  (weightedMonomialSpan_eq_power G hG n).ge

end UnitDistance.GroupAugmentation
