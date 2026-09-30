module

public import UnitDistance.JenningsGroupNormalForm
public import UnitDistance.JenningsBinaryWords

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual homogeneous generators of a finite 2-group

Lists of lifted bases are concatenated in increasing augmentation degree.
The ordered binary products cover the group, and the number of binary
coordinates is exactly the sum of the actual layer ranks. All group and
filtration assertions here follow from the constructed layer normal forms.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (G : Type*) [Group G] [Finite G]

local instance positiveDegreeFact (i : ℕ) : Fact (1 ≤ i+1) :=
  ⟨Nat.succ_le_succ (Nat.zero_le i)⟩

/-- Actual lifted homogeneous group directions in one positive layer. -/
def layerGenerators (i : ℕ) : List G := by
  letI : Fact (1 ≤ i+1) := ⟨Nat.succ_le_succ (Nat.zero_le i)⟩
  exact List.ofFn (fun j : Fin (layerRank G (i+1)) => (layerBasisLift G (i+1) j : G))

@[simp] theorem length_layerGenerators (i : ℕ) :
    (layerGenerators G i).length = positiveLayerRank G i := by
  unfold layerGenerators positiveLayerRank
  rw [List.length_ofFn]

/-- Concatenated actual homogeneous directions over a finite interval of layers. -/
def generatorsFrom (start length : ℕ) : List G :=
  (List.ofFn (fun i : Fin length => layerGenerators G (start+i.val))).flatten

@[simp] theorem generatorsFrom_zero (start : ℕ) : generatorsFrom G start 0 = [] := by
  simp [generatorsFrom]

@[simp] theorem generatorsFrom_succ (start length : ℕ) :
    generatorsFrom G start (length+1) = layerGenerators G start ++ generatorsFrom G (start+1) length := by
  simp [generatorsFrom, List.ofFn_succ, Nat.add_left_comm, Nat.add_comm]

/-- The length counts actual dimensions of the actual layers. -/
theorem length_generatorsFrom (start length : ℕ) :
    (generatorsFrom G start length).length =
      ∑ i ∈ Finset.range length, positiveLayerRank G (start+i) := by
  simp only [generatorsFrom, List.length_flatten, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, length_layerGenerators]
  exact Fin.sum_univ_eq_sum_range (fun j => positiveLayerRank G (start+j)) length

/-- Every chosen layer section is an ordered binary word in that layer's
actual basis lifts. The exponents are literally zero or one. -/
theorem orderedLayerSection_mem_words (i : ℕ)
    (v : BinaryLayer G i) :
    (orderedLayerSection G (i+1) (show LayerVector G (i+1) from v) : G) ∈
      Jennings.binaryWords (layerGenerators G i) := by
  letI : Fact (1 ≤ i+1) := ⟨Nat.succ_le_succ (Nat.zero_le i)⟩
  change LayerVector G (i+1) at v
  change (dimensionSubgroup (ZMod 2) G (i+1)).subtype
    ((List.ofFn (fun j : Fin (layerRank G (i+1)) =>
      layerBasisLift G (i+1) j ^ (((layerBasis G (i+1)).repr v j).val))).prod) ∈ _
  rw [map_list_prod, List.map_ofFn]
  apply Jennings.ofFn_prod_mem_binaryWords
  intro j
  have hc : ((layerBasis G (i+1)).repr v j).val = 0 ∨
      ((layerBasis G (i+1)).repr v j).val = 1 := by
    have ht := ZMod.val_lt ((layerBasis G (i+1)).repr v j)
    omega
  rcases hc with hc | hc
  · left; simp [hc]
  · right; simp [hc]

/-- If the terminal actual dimension subgroup vanishes, ordered binary
words in the intervening lifted directions cover the whole initial subgroup. -/
theorem mem_words_generatorsFrom (length start : ℕ)
    (hend : dimensionSubgroup (ZMod 2) G (start+length+1) = ⊥)
    (g : G) (hg : g ∈ dimensionSubgroup (ZMod 2) G (start+1)) :
    g ∈ Jennings.binaryWords (generatorsFrom G start length) := by
  induction length generalizing start g with
  | zero =>
    have he : dimensionSubgroup (ZMod 2) G (start+1) = ⊥ := by simpa using hend
    rw [he, Subgroup.mem_bot] at hg
    simp [hg]
  | succ length ih =>
    letI : Fact (1 ≤ start+1) := ⟨Nat.succ_le_succ (Nat.zero_le start)⟩
    have htail : dimensionSubgroup (ZMod 2) G ((start+1)+length+1) = ⊥ := by
      have he : (start+1)+length+1 = start+(length+1)+1 := by omega
      rw [he]
      exact hend
    obtain ⟨⟨v,h⟩,he⟩ := (orderedLayerCoordinatesNext G (start+1)).surjective ⟨g,hg⟩
    rw [generatorsFrom_succ, Jennings.binaryWords_append]
    refine ⟨(orderedLayerSection G (start+1) v : G),
      orderedLayerSection_mem_words G start v, (h : G), ih (start+1) htail h h.property, ?_⟩
    exact congrArg Subtype.val he

/-- The full list of actual homogeneous group directions. -/
def homogeneousGenerators : List G := generatorsFrom G 0 (Nat.card G)

/-- Every group element is an ordered binary word in the actual homogeneous
list. This is a proved group normal-form consequence, not a basis hypothesis. -/
theorem binaryWords_homogeneousGenerators (hG : IsPGroup 2 G) :
    Jennings.binaryWords (homogeneousGenerators G) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  apply mem_words_generatorsFrom G (Nat.card G) 0
  · simpa only [Nat.zero_add] using
      dimensionSubgroup_eq_bot_of_card_le G 2 hG (Nat.card G+1) (Nat.le_succ _)
  · simp

/-- The binary word count equals the actual group order. -/
theorem two_pow_length_homogeneousGenerators (hG : IsPGroup 2 G) :
    2 ^ (homogeneousGenerators G).length = Nat.card G := by
  rw [homogeneousGenerators, length_generatorsFrom]
  simp only [Nat.zero_add]
  exact (card_eq_two_pow_sum_layerRanks G hG).symm

end UnitDistance.GroupAugmentation
