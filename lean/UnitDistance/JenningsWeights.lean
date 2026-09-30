module

public import UnitDistance.JenningsAugmentationBasis

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual augmentation degrees and the weighted monomial span inclusion

A nonidentity group element's degree is the largest actual dimension-subgroup
degree containing it, defined by the first subgroup not containing it.
Existence of that first failure follows from the proved finite p-group
nilpotence. The homogeneous lifts have precisely their layer degrees.
Products of their differences therefore lie in the sum of their degrees.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (G : Type*) [Group G] [Finite G]

theorem exists_not_mem_dimensionSubgroup (hG : IsPGroup 2 G) (g : G) (hg : g ≠ 1) :
    ∃ n, g ∉ dimensionSubgroup (ZMod 2) G n := by
  refine ⟨Nat.card G, ?_⟩
  rw [dimensionSubgroup_eq_bot_of_card_le G 2 hG _ (le_refl _), Subgroup.mem_bot]
  exact hg

/-- The ordinary augmentation-dimension degree of a group element.
The identity is assigned degree zero; all its differences are zero anyway. -/
def groupDegree (hG : IsPGroup 2 G) (g : G) : ℕ := by
  classical
  exact if hg : g = 1 then 0 else Nat.find (exists_not_mem_dimensionSubgroup G hG g hg) - 1

@[simp] theorem groupDegree_one (hG : IsPGroup 2 G) : groupDegree G hG 1 = 0 := by
  simp [groupDegree]

/-- A group element belongs to its independently defined actual degree. -/
theorem mem_dimensionSubgroup_groupDegree (hG : IsPGroup 2 G) (g : G) :
    g ∈ dimensionSubgroup (ZMod 2) G (groupDegree G hG g) := by
  classical
  by_cases hg : g = 1
  · subst g; simp
  · rw [groupDegree, dif_neg hg]
    let hex := exists_not_mem_dimensionSubgroup G hG g hg
    have hpos : 0 < Nat.find hex := by
      by_contra hn
      have hz : Nat.find hex = 0 := by omega
      have ht := Nat.find_spec hex
      rw [hz, dimensionSubgroup_zero] at ht
      exact ht (Subgroup.mem_top _)
    by_contra hbad
    have ht := Nat.find_min' hex hbad
    omega

/-- Every witnessed exact degree is equal to the independently defined one. -/
theorem groupDegree_eq_of_mem_not_mem (hG : IsPGroup 2 G) (g : G) (n : ℕ)
    (hg : g ∈ dimensionSubgroup (ZMod 2) G n)
    (hnext : g ∉ dimensionSubgroup (ZMod 2) G (n+1)) : groupDegree G hG g = n := by
  classical
  have hne : g ≠ 1 := by intro he; subst g; exact hnext (Subgroup.one_mem _)
  rw [groupDegree, dif_neg hne]
  let hex := exists_not_mem_dimensionSubgroup G hG g hne
  have hu : Nat.find hex ≤ n+1 := Nat.find_min' hex hnext
  have hl : n < Nat.find hex := by
    by_contra hbad
    have hn : Nat.find hex ≤ n := by omega
    exact Nat.find_spec hex (dimensionSubgroup_antitone (ZMod 2) G hn hg)
  omega

/-- The actual lifted homogeneous basis elements have their stated degrees. -/
theorem groupDegree_layerBasisLift (hG : IsPGroup 2 G) (n : ℕ) [Fact (1 ≤ n)]
    (i : Fin (layerRank G n)) : groupDegree G hG (layerBasisLift G n i : G) = n :=
  groupDegree_eq_of_mem_not_mem G hG _ n (layerBasisLift G n i).property
    (layerBasisLift_not_mem_next G n i)

/-- The actual group letter corresponding to a basis-monomial position. -/
def monomialLetter (i : Fin (homogeneousDifferences G).length) : G :=
  (homogeneousGenerators G).get ⟨i.val, by simpa [homogeneousDifferences] using i.isLt⟩

@[simp] theorem get_homogeneousDifferences (i : Fin (homogeneousDifferences G).length) :
    (homogeneousDifferences G).get i = delta (ZMod 2) (monomialLetter G i) - 1 := by
  have hi : i.val < (homogeneousGenerators G).length := by
    simpa [homogeneousDifferences] using i.isLt
  change (List.map (fun g : G => delta (ZMod 2) g - 1)
      (homogeneousGenerators G))[i.val] =
    delta (ZMod 2) ((homogeneousGenerators G)[i.val]'hi) - 1
  exact List.getElem_map _

/-- Weights are actual augmentation degrees of the actual group letters. -/
def monomialWeight (hG : IsPGroup 2 G) (c : Fin (homogeneousDifferences G).length → Bool) : ℕ :=
  ∑ i, if c i then groupDegree G hG (monomialLetter G i) else 0

variable (R : Type*) [CommRing R]

omit [Finite G] in
/-- Ordered products add actual augmentation degrees in a noncommutative
algebra; no reordering is used for this inclusion. -/
theorem ofFn_prod_mem_power {k : ℕ} (a : Fin k → A R G) (w : Fin k → ℕ)
    (ha : ∀ i, a i ∈ power R G (w i)) :
    (List.ofFn a).prod ∈ power R G (∑ i, w i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact mul_mem_add R G (ha 0) (ih (fun i => a i.succ) (fun i => w i.succ) (fun i => ha i.succ))

/-- Every actual augmentation basis monomial belongs to the actual power
specified by the sum of its independently defined homogeneous degrees. -/
theorem augmentationMonomial_mem_weight (hG : IsPGroup 2 G)
    (c : Fin (homogeneousDifferences G).length → Bool) :
    augmentationMonomial G c ∈ power (ZMod 2) G (monomialWeight G hG c) := by
  apply ofFn_prod_mem_power G (ZMod 2)
  intro i
  cases c i with
  | false => simp
  | true =>
    change (homogeneousDifferences G).get i ∈
      power (ZMod 2) G (groupDegree G hG (monomialLetter G i))
    rw [get_homogeneousDifferences]
    exact mem_dimensionSubgroup_groupDegree G hG (monomialLetter G i)

/-- Span of the actual basis monomials at or above the chosen weight. -/
def weightedMonomialSpan (hG : IsPGroup 2 G) (n : ℕ) : Submodule (ZMod 2) (A (ZMod 2) G) :=
  Submodule.span (ZMod 2) {a | ∃ c, n ≤ monomialWeight G hG c ∧ a = augmentationMonomial G c}

/-- The forward inclusion in the exact weighted Jennings filtration theorem. -/
theorem weightedMonomialSpan_le_power (hG : IsPGroup 2 G) (n : ℕ) :
    weightedMonomialSpan G hG n ≤ power (ZMod 2) G n := by
  apply Submodule.span_le.mpr
  rintro a ⟨c,hc,rfl⟩
  exact power_antitone (ZMod 2) G hc (augmentationMonomial_mem_weight G hG c)

end UnitDistance.GroupAugmentation
