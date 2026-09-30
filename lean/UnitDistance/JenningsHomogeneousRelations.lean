module

public import UnitDistance.JenningsCollection
public import UnitDistance.JenningsWeights
public import UnitDistance.JenningsInitialForms

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual homogeneous collection relations for every finite 2-group

The letters and weights are the actual dimension-layer representatives.
The coefficients are derived from actual quotient-vector coordinates.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.JenningsCollection
open GroupAugmentation
variable (R G ι : Type*) [CommRing R] [Group G] [LinearOrder ι] [Fintype ι]
variable (x : ι → A R G) (w : ι → ℕ)

/-- Linear span of actual letters of exactly the given homogeneous degree. -/
def homogeneousLinearSpan (d : ℕ) : Submodule R (A R G) :=
  Submodule.span R {a | ∃ i, w i = d ∧ a = x i}

omit [LinearOrder ι] in
/-- A homogeneous span has finite coefficients supported at that degree. -/
theorem exists_homogeneous_coefficients (d : ℕ) (a : A R G)
    (ha : a ∈ homogeneousLinearSpan R G ι x w d) :
    ∃ c : ι → R, (∀ i, c i ≠ 0 → w i = d) ∧ ∑ i, c i • x i = a := by
  classical
  let y : ι → A R G := fun i => if w i = d then x i else 0
  have hle : homogeneousLinearSpan R G ι x w d ≤ Submodule.span R (Set.range y) := by
    apply Submodule.span_le.mpr
    rintro a ⟨i,hi,rfl⟩
    apply Submodule.subset_span
    exact ⟨i, by simp [y,hi]⟩
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hle ha)
  refine ⟨fun i => if w i = d then c i else 0, ?_, ?_⟩
  · intro i hi
    by_contra he
    simp [he] at hi
  · convert hc using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : w i = d <;> simp [y,hi]

/-- Literal homogeneous remainders supply the finite collection coefficients. -/
def Relations.of_remainders
    (hc : ∀ i j, ∃ a ∈ homogeneousLinearSpan R G ι x w (w i+w j),
      x i*x j - x j*x i - a ∈ power R G (w i+w j+1))
    (hs : ∀ i, ∃ a ∈ homogeneousLinearSpan R G ι x w (2*w i),
      x i*x i - a ∈ power R G (2*w i+1)) : Relations R G ι x w := by
  classical
  choose ac hac hec using hc
  choose as has hes using hs
  choose cc hcc hsumc using fun i j =>
    exists_homogeneous_coefficients R G ι x w (w i+w j) (ac i j) (hac i j)
  choose cs hcs hsums using fun i =>
    exists_homogeneous_coefficients R G ι x w (2*w i) (as i) (has i)
  exact {
    commutator := cc
    commutator_support := hcc
    commutator_error := by intro i j; rw [hsumc]; exact hec i j
    square := cs
    square_support := hcs
    square_error := by intro i; rw [hsums]; exact hes i }

end UnitDistance.JenningsCollection

namespace UnitDistance.GroupAugmentation
variable (G : Type*) [Group G] [Finite G] (hG : IsPGroup 2 G)

local instance homogeneousRelationPositiveDegreeFact (i : ℕ) : Fact (1 ≤ i+1) := ⟨by omega⟩

include hG in
/-- Each genuine basis lift occurs in the finite homogeneous list. -/
theorem layerBasisLift_mem_homogeneousGenerators (n : ℕ) [Fact (1 ≤ n)]
    (i : Fin (layerRank G n)) :
    (layerBasisLift G n i : G) ∈ homogeneousGenerators G := by
  have hn : n < Nat.card G := by
    by_contra hn
    have ht := (layerBasisLift G n i).property
    have he := (dimensionSubgroup_eq_bot_of_card_le G 2 hG n (by omega)).le ht
    have he' : (layerBasisLift G n i : G) = 1 := Subgroup.mem_bot.mp he
    exact layerBasisLift_not_mem_next G n i (he' ▸ Subgroup.one_mem _)
  have hn0 : 1 ≤ n := Fact.out
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply List.mem_flatten.mpr
  refine ⟨layerGenerators G m, ?_, ?_⟩
  · apply List.mem_ofFn.mpr
    exact ⟨⟨m,by omega⟩, by simp⟩
  · exact List.mem_ofFn.mpr ⟨i,rfl⟩

/-- A list position is an actual basis direction of some positive layer. -/
theorem monomialLetter_has_layer (i : Fin (homogeneousDifferences G).length) :
    ∃ n, ∃ hn : Fact (1 ≤ n), ∃ j : Fin (@layerRank G _ n hn),
      monomialLetter G i = (@layerBasisLift G _ _ n hn j : G) := by
  have hmem : monomialLetter G i ∈ homogeneousGenerators G := List.get_mem _ _
  obtain ⟨l,hl,hg⟩ := List.mem_flatten.mp hmem
  obtain ⟨n,rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hg
  exact ⟨0+n.val+1, inferInstance, j, hj.symm⟩

/-- All actual homogeneous letters have strictly positive actual degree. -/
theorem monomialLetter_degree_pos (i : Fin (homogeneousDifferences G).length) :
    1 ≤ groupDegree G hG (monomialLetter G i) := by
  obtain ⟨n,hn,j,hj⟩ := monomialLetter_has_layer G i
  letI := hn
  rw [hj, groupDegree_layerBasisLift]
  exact hn.out

/-- Every lifted basis difference is one of the actual positional letters,
and the positional weight is its exact degree. -/
theorem exists_letter_of_layer (n : ℕ) [Fact (1 ≤ n)] (j : Fin (layerRank G n)) :
    ∃ i : Fin (homogeneousDifferences G).length,
      (homogeneousDifferences G).get i = delta (ZMod 2) (layerBasisLift G n j : G)-1 ∧
      groupDegree G hG (monomialLetter G i) = n := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (layerBasisLift_mem_homogeneousGenerators G hG n j)
  let k : Fin (homogeneousDifferences G).length := ⟨i.val, by simp [homogeneousDifferences]⟩
  have hk : monomialLetter G k = (layerBasisLift G n j : G) := hi
  refine ⟨k, ?_, ?_⟩
  · rw [get_homogeneousDifferences,hk]
  · rw [hk,groupDegree_layerBasisLift]

/-- The independently computed quotient initial difference is spanned by
actual positional letters of precisely its homogeneous degree. -/
theorem initialDifference_mem_homogeneousLinearSpan (n : ℕ) [Fact (1 ≤ n)]
    (g : dimensionSubgroup (ZMod 2) G n) :
    initialDifference G n g ∈ JenningsCollection.homogeneousLinearSpan (ZMod 2) G
      (Fin (homogeneousDifferences G).length) (fun i => (homogeneousDifferences G).get i)
      (fun i => groupDegree G hG (monomialLetter G i)) n := by
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  obtain ⟨i,hi,hw⟩ := exists_letter_of_layer G hG n j
  exact Submodule.subset_span ⟨i,hw,hi.symm⟩

/-- Actual homogeneous commutator and square relations exist for every finite
2-group, derived from the actual dimension-layer initial forms. -/
def homogeneousRelations : JenningsCollection.Relations (ZMod 2) G
    (Fin (homogeneousDifferences G).length) (fun i => (homogeneousDifferences G).get i)
    (fun i => groupDegree G hG (monomialLetter G i)) := by
  apply JenningsCollection.Relations.of_remainders
  · intro i j
    let m := groupDegree G hG (monomialLetter G i)
    let n := groupDegree G hG (monomialLetter G j)
    let g : dimensionSubgroup (ZMod 2) G m :=
      ⟨monomialLetter G i, mem_dimensionSubgroup_groupDegree G hG _⟩
    let h : dimensionSubgroup (ZMod 2) G n :=
      ⟨monomialLetter G j, mem_dimensionSubgroup_groupDegree G hG _⟩
    letI : Fact (1 ≤ m+n) := ⟨by
      have hm := monomialLetter_degree_pos G hG i
      dsimp [m,n]
      omega⟩
    let c : dimensionSubgroup (ZMod 2) G (m+n) :=
      ⟨(g:G)*(h:G)*(g:G)⁻¹*(h:G)⁻¹, commutator_mem (ZMod 2) G g.property h.property⟩
    refine ⟨initialDifference G (m+n) c,
      initialDifference_mem_homogeneousLinearSpan G hG (m+n) c, ?_⟩
    simp only [get_homogeneousDifferences]
    exact commutator_initial_form G n m g h
  · intro i
    let n := groupDegree G hG (monomialLetter G i)
    let g : dimensionSubgroup (ZMod 2) G n :=
      ⟨monomialLetter G i, mem_dimensionSubgroup_groupDegree G hG _⟩
    letI : Fact (1 ≤ 2*n) := ⟨by
      have hn := monomialLetter_degree_pos G hG i
      dsimp [n]
      omega⟩
    let c : dimensionSubgroup (ZMod 2) G (2*n) :=
      ⟨(g:G)^2, square_mem (ZMod 2) G g.property⟩
    refine ⟨initialDifference G (2*n) c,
      initialDifference_mem_homogeneousLinearSpan G hG (2*n) c, ?_⟩
    simp only [get_homogeneousDifferences]
    exact square_initial_form G n g

end UnitDistance.GroupAugmentation
