module

public import UnitDistance.JenningsAdaptedLayers
public import UnitDistance.JenningsOrderedBasis

@[expose] public section
set_option backward.privateInPublic true


/-!
# Complementary directions before all prescribed subgroup directions

Actual injective dimension-layer maps extend the local layer bases. The
resulting finite ambient list puts every complementary direction first and
then includes the whole original local homogeneous list, in its original
order. Its actual homogeneous spans and exact count are proved here.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (D P : Type*) [Group D] [Group P] [Finite D] [Finite P]
variable (f : D →* P)
variable (hinj : ∀ n, Function.Injective (layerMap (ZMod 2) D f n))

local instance adaptedPositiveDegreeFact (i : ℕ) : Fact (1 ≤ i+1) := ⟨by omega⟩

/-- Complementary actual group representatives in one positive layer. -/
def layerComplementGenerators (i : ℕ) : List P := by
  letI : Fintype (LayerComplement D P f (i+1) (hinj (i+1))) := Fintype.ofFinite _
  exact List.ofFn (fun j : Fin (Fintype.card (LayerComplement D P f (i+1) (hinj (i+1)))) =>
    (adaptedLayerLift D P f (i+1) (hinj (i+1))
      (Sum.inl ((Fintype.equivFin _).symm j)) : P))

@[simp] theorem length_layerComplementGenerators (i : ℕ) :
    (layerComplementGenerators D P f hinj i).length =
      Nat.card (LayerComplement D P f (i+1) (hinj (i+1))) := by
  simp [layerComplementGenerators,Nat.card_eq_fintype_card]

/-- A common finite cutoff beyond termination of both actual filtrations. -/
def adaptedLayerCutoff : ℕ := Nat.card D + Nat.card P

/-- All complementary directions, ordered by their ambient degree. -/
def complementGenerators : List P :=
  (List.ofFn (fun i : Fin (adaptedLayerCutoff D P) =>
    layerComplementGenerators D P f hinj i.val)).flatten

/-- Every original local homogeneous representative occurs last, with its
original order and actual group image retained literally. -/
def adaptedGenerators : List P :=
  complementGenerators D P f hinj ++ (homogeneousGenerators D).map f

@[simp] theorem length_complementGenerators :
    (complementGenerators D P f hinj).length =
      ∑ i ∈ Finset.range (adaptedLayerCutoff D P),
        Nat.card (LayerComplement D P f (i+1) (hinj (i+1))) := by
  simp only [complementGenerators,List.length_flatten,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,length_layerComplementGenerators]
  exact Fin.sum_univ_eq_sum_range
    (fun i => Nat.card (LayerComplement D P f (i+1) (hinj (i+1)))) (adaptedLayerCutoff D P)

/-- Every complementary basis direction occurs in the chosen finite list. -/
theorem adaptedLayerLift_inl_mem_complementGenerators (hP : IsPGroup 2 P)
    (n : ℕ) [Fact (1 ≤ n)] (j : LayerComplement D P f n (hinj n)) :
    (adaptedLayerLift D P f n (hinj n) (Sum.inl j) : P) ∈
      complementGenerators D P f hinj := by
  have hn : n < Nat.card P := by
    by_contra hn
    have ht := (adaptedLayerLift D P f n (hinj n) (Sum.inl j)).property
    have he := (dimensionSubgroup_eq_bot_of_card_le P 2 hP n (by omega)).le ht
    have he' : (adaptedLayerLift D P f n (hinj n) (Sum.inl j) : P) = 1 :=
      Subgroup.mem_bot.mp he
    exact adaptedLayerLift_not_mem_next D P f n (hinj n) (Sum.inl j)
      (he' ▸ Subgroup.one_mem _)
  have hn0 : 1 ≤ n := Fact.out
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply List.mem_flatten.mpr
  refine ⟨layerComplementGenerators D P f hinj m,?_,?_⟩
  · apply List.mem_ofFn.mpr
    exact ⟨⟨m,by dsimp [adaptedLayerCutoff]; omega⟩,rfl⟩
  · letI : Fintype (LayerComplement D P f (m+1) (hinj (m+1))) := Fintype.ofFinite _
    apply List.mem_ofFn.mpr
    exact ⟨(Fintype.equivFin _) j,by simp⟩

/-- Each extended layer basis lift occurs among the actual ambient letters. -/
theorem adaptedLayerLift_mem_adaptedGenerators (hD : IsPGroup 2 D) (hP : IsPGroup 2 P)
    (n : ℕ) [Fact (1 ≤ n)]
    (j : LayerComplement D P f n (hinj n) ⊕ Fin (layerRank D n)) :
    (adaptedLayerLift D P f n (hinj n) j : P) ∈ adaptedGenerators D P f hinj := by
  cases j with
  | inl j =>
    exact List.mem_append_left _
      (adaptedLayerLift_inl_mem_complementGenerators D P f hinj hP n j)
  | inr j =>
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨(layerBasisLift D n j : D),
      layerBasisLift_mem_homogeneousGenerators D hD n j,rfl⟩

/-- Every selected letter is an actual nonzero direction of a positive
ambient layer, including the prescribed local letters. -/
theorem mem_adaptedGenerators_has_layer (a : P) (ha : a ∈ adaptedGenerators D P f hinj) :
    ∃ n, ∃ hn : Fact (1 ≤ n),
      ∃ j : LayerComplement D P f n (hinj n) ⊕ Fin (@layerRank D _ n hn),
        a = (@adaptedLayerLift D P _ _ _ f n hn (hinj n) j : P) := by
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨l,hl,ha⟩ := List.mem_flatten.mp ha
    obtain ⟨n,rfl⟩ := List.mem_ofFn.mp hl
    letI : Fintype (LayerComplement D P f (n.val+1) (hinj (n.val+1))) := Fintype.ofFinite _
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp ha
    exact ⟨n.val+1,inferInstance,Sum.inl ((Fintype.equivFin _).symm j),hj.symm⟩
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    obtain ⟨l,hl,hb⟩ := List.mem_flatten.mp hb
    obtain ⟨n,rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hb
    refine ⟨0+n.val+1,inferInstance,Sum.inr j,?_⟩
    exact congrArg f hj.symm

/-- The complementary and local positions remain separate finite blocks. -/
abbrev adaptedGeneratorCount : ℕ :=
  (complementGenerators D P f hinj).length + (homogeneousGenerators D).length

/-- Positional ambient generators, in complement-first/local-last order. -/
def adaptedLetter (i : Fin (adaptedGeneratorCount D P f hinj)) : P :=
  Fin.addCases ((complementGenerators D P f hinj).get)
    (fun j => f ((homogeneousGenerators D).get j)) i

theorem adaptedLetter_mem_adaptedGenerators
    (i : Fin (adaptedGeneratorCount D P f hinj)) :
    adaptedLetter D P f hinj i ∈ adaptedGenerators D P f hinj := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [adaptedLetter,Fin.addCases_left,adaptedGenerators] using
      List.mem_append_left ((homogeneousGenerators D).map f)
        (List.get_mem (complementGenerators D P f hinj) j)
  · intro j
    simpa only [adaptedLetter,Fin.addCases_right,adaptedGenerators] using
      List.mem_append_right (complementGenerators D P f hinj)
      (List.mem_map.mpr ⟨_,List.get_mem (homogeneousGenerators D) j,rfl⟩ :
        f ((homogeneousGenerators D).get j) ∈ (homogeneousGenerators D).map f)

theorem exists_adaptedLetter_of_mem (a : P) (ha : a ∈ adaptedGenerators D P f hinj) :
    ∃ i, adaptedLetter D P f hinj i = a := by
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨j,hj⟩ := List.mem_iff_get.mp ha
    exact ⟨Fin.castAdd (homogeneousGenerators D).length j,by simpa [adaptedLetter] using hj⟩
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hb
    exact ⟨Fin.natAdd (complementGenerators D P f hinj).length j,
      by simpa only [adaptedLetter,Fin.addCases_right] using congrArg f hj⟩

theorem adaptedLetter_degree_pos (hP : IsPGroup 2 P)
    (i : Fin (adaptedGeneratorCount D P f hinj)) :
    1 ≤ groupDegree P hP (adaptedLetter D P f hinj i) := by
  obtain ⟨n,hn,j,hj⟩ := mem_adaptedGenerators_has_layer D P f hinj _
    (adaptedLetter_mem_adaptedGenerators D P f hinj i)
  letI := hn
  rw [show adaptedLetter D P f hinj i = _ from hj,adaptedLayerLift_degree]
  exact hn.out

/-- The actual extended initial forms are spanned by positional letters of
exactly the same independently defined ambient degree. -/
theorem adaptedInitialDifference_mem_homogeneousLinearSpan
    (hD : IsPGroup 2 D) (hP : IsPGroup 2 P) (n : ℕ) [Fact (1 ≤ n)]
    (a : dimensionSubgroup (ZMod 2) P n) :
    adaptedInitialDifference D P f n (hinj n) a ∈
      JenningsCollection.homogeneousLinearSpan (ZMod 2) P
        (Fin (adaptedGeneratorCount D P f hinj))
        (fun i => delta (ZMod 2) (adaptedLetter D P f hinj i)-1)
        (fun i => groupDegree P hP (adaptedLetter D P f hinj i)) n := by
  letI : Fintype (LayerComplement D P f n (hinj n) ⊕ Fin (layerRank D n)) := Fintype.ofFinite _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  obtain ⟨i,hi⟩ := exists_adaptedLetter_of_mem D P f hinj _
    (adaptedLayerLift_mem_adaptedGenerators D P f hinj hD hP n j)
  apply Submodule.subset_span
  refine ⟨i,?_,?_⟩
  · dsimp only
    rw [hi,adaptedLayerLift_degree]
  · change delta (ZMod 2) (adaptedLayerLift D P f n (hinj n) j : P)-1 =
      delta (ZMod 2) (adaptedLetter D P f hinj i)-1
    rw [hi]

/-- The actual complementary and prescribed local letters span every
actual ambient dimension layer; no adapted-basis hypothesis is assumed. -/
theorem adaptedLetters_spansActualLayers (hD : IsPGroup 2 D) (hP : IsPGroup 2 P) :
    SpansActualLayers P (Fin (adaptedGeneratorCount D P f hinj))
      (adaptedLetter D P f hinj) (fun i => groupDegree P hP (adaptedLetter D P f hinj i)) := by
  intro n hn a
  letI : Fact (1 ≤ n) := ⟨hn⟩
  exact ⟨adaptedInitialDifference D P f n (hinj n) a,
    adaptedInitialDifference_mem_homogeneousLinearSpan D P f hinj hD hP n a,
    difference_sub_adaptedInitial_mem D P f n (hinj n) a⟩

omit f hinj in
/-- The actual layer-cardinality formula is valid at any proven terminal
cutoff, so local and ambient sums may use the same finite interval. -/
theorem card_eq_two_pow_sum_layerRanks_at (G : Type*) [Group G] [Finite G]
    (hG : IsPGroup 2 G) (N : ℕ) (hN : Nat.card G ≤ N+1) :
    Nat.card G = 2 ^ (∑ i ∈ Finset.range N, positiveLayerRank G i) := by
  have ht := card_dimensionSubgroup_telescope G N
  rw [dimensionSubgroup_eq_bot_of_card_le G 2 hG (N+1) hN,Subgroup.card_bot,mul_one] at ht
  exact ht

/-- Adding exactly the complementary layer directions gives the ambient
number of binary coordinates. The local list keeps its original length. -/
theorem two_pow_length_adaptedGenerators (hD : IsPGroup 2 D) (hP : IsPGroup 2 P) :
    2 ^ (adaptedGenerators D P f hinj).length = Nat.card P := by
  have hlocal : (homogeneousGenerators D).length =
      ∑ i ∈ Finset.range (adaptedLayerCutoff D P), positiveLayerRank D i := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    dsimp only
    rw [two_pow_length_homogeneousGenerators D hD]
    exact card_eq_two_pow_sum_layerRanks_at D hD _ (by dsimp [adaptedLayerCutoff]; omega)
  have hsum :
      (∑ i ∈ Finset.range (adaptedLayerCutoff D P),
        Nat.card (LayerComplement D P f (i+1) (hinj (i+1)))) +
        (∑ i ∈ Finset.range (adaptedLayerCutoff D P), positiveLayerRank D i) =
      ∑ i ∈ Finset.range (adaptedLayerCutoff D P), positiveLayerRank P i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact card_layerComplement_add_rank D P f (i+1) (hinj (i+1))
  rw [adaptedGenerators,List.length_append,List.length_map,length_complementGenerators,hlocal,hsum]
  exact (card_eq_two_pow_sum_layerRanks_at P hP _ (by dsimp [adaptedLayerCutoff]; omega)).symm

theorem two_pow_adaptedGeneratorCount (hD : IsPGroup 2 D) (hP : IsPGroup 2 P) :
    2 ^ adaptedGeneratorCount D P f hinj = Nat.card P := by
  simpa only [adaptedGenerators,List.length_append,List.length_map,adaptedGeneratorCount] using
    two_pow_length_adaptedGenerators D P f hinj hD hP

/-- The constructed complement-first/local-last family has the exact
weighted augmentation filtration, in every degree. -/
theorem adaptedBinarySpan_eq_power (hD : IsPGroup 2 D) (hP : IsPGroup 2 P) (n : ℕ) :
    JenningsCollection.binarySpan (ZMod 2) P (adaptedGeneratorCount D P f hinj)
      (fun i => delta (ZMod 2) (adaptedLetter D P f hinj i)-1)
      (fun i => groupDegree P hP (adaptedLetter D P f hinj i)) n =
      power (ZMod 2) P n :=
  binarySpan_eq_power_of_spansActualLayers P hP _ _ _
    (adaptedLetter_degree_pos D P f hinj hP)
    (fun i => mem_dimensionSubgroup_groupDegree P hP _)
    (adaptedLetters_spansActualLayers D P f hinj hD hP) n

/-- An actual ambient augmentation basis, with all original local factors
after all complementary factors. This is a proved construction. -/
def adaptedAugmentationBasis (hD : IsPGroup 2 D) (hP : IsPGroup 2 P) :
    Module.Basis (Fin (adaptedGeneratorCount D P f hinj) → Bool)
      (ZMod 2) (A (ZMod 2) P) :=
  homogeneousBinaryBasis P hP _ (adaptedLetter D P f hinj)
    (fun i => groupDegree P hP (adaptedLetter D P f hinj i))
    (adaptedLetter_degree_pos D P f hinj hP)
    (fun i => mem_dimensionSubgroup_groupDegree P hP _)
    (adaptedLetters_spansActualLayers D P f hinj hD hP)
    (two_pow_adaptedGeneratorCount D P f hinj hD hP)

@[simp] theorem adaptedAugmentationBasis_apply (hD : IsPGroup 2 D) (hP : IsPGroup 2 P)
    (c : Fin (adaptedGeneratorCount D P f hinj) → Bool) :
    adaptedAugmentationBasis D P f hinj hD hP c =
      JenningsCollection.binaryMonomial (ZMod 2) P (adaptedGeneratorCount D P f hinj)
        (fun i => delta (ZMod 2) (adaptedLetter D P f hinj i)-1) c := by
  simp [adaptedAugmentationBasis]

end UnitDistance.GroupAugmentation
