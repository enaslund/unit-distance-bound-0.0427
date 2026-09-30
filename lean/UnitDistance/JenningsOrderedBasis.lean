module

public import UnitDistance.JenningsBasisChange

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual binary augmentation bases in any order

Homogeneous spanning of the actual group layers gives the exact weighted
power spans. The proved group order then supplies linear independence when
the chosen directions have the correct total count.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.JenningsCollection
open GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G] (r : ℕ)
variable (x : Fin r → A R G) (w : Fin r → ℕ)

/-- Binary products preserve the chosen order of their actual factors. -/
def binaryMonomial (c : Fin r → Bool) : A R G :=
  (List.ofFn (fun i => if c i then x i else 1)).prod

/-- The sum of the weights of the factors actually selected. -/
def binaryWeight (c : Fin r → Bool) : ℕ := ∑ i, if c i then w i else 0

def binarySpan (n : ℕ) : Submodule R (A R G) :=
  Submodule.span R {a | ∃ c, n ≤ binaryWeight r w c ∧ a = binaryMonomial R G r x c}

/-- Ordered lists and binary coordinates give exactly the same vectors
and weights, for an arbitrary finite ordered family. -/
theorem orderedSpan_eq_binarySpan (n : ℕ) :
    orderedSpan R G (Fin r) x w n = binarySpan R G r x w n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro a ⟨l,hl,hw,rfl⟩
    let c : Fin r → Bool := fun i => decide (i ∈ l)
    have he := increasing_eq_filter_finRange l hl
    have hv : wordValue R G (Fin r) x l = binaryMonomial R G r x c := by
      change (l.map _).prod = (List.ofFn _).prod
      rw [he,filter_map_prod,← List.ofFn_eq_map]
    have hd : wordDegree (Fin r) w l = binaryWeight r w c := by
      change (l.map _).sum = ∑ i, _
      rw [he,filter_map_sum,← List.ofFn_eq_map,List.sum_ofFn]
    exact Submodule.subset_span ⟨c,hd ▸ hw,hv⟩
  · apply Submodule.span_le.mpr
    rintro a ⟨c,hc,rfl⟩
    let l := (List.finRange r).filter c
    have hv : binaryMonomial R G r x c = wordValue R G (Fin r) x l := by
      change (List.ofFn _).prod = (((List.finRange r).filter c).map _).prod
      rw [filter_map_prod,← List.ofFn_eq_map]
    have hd : binaryWeight r w c = wordDegree (Fin r) w l := by
      change (∑ i, _) = (((List.finRange r).filter c).map _).sum
      rw [filter_map_sum,← List.ofFn_eq_map,List.sum_ofFn]
    exact Submodule.subset_span ⟨l,(List.sortedLT_finRange _).pairwise.filter _,hd ▸ hc,hv⟩

@[simp] theorem binarySpan_zero :
    binarySpan R G r x w 0 = Submodule.span R (Set.range (binaryMonomial R G r x)) := by
  unfold binarySpan
  congr 1
  ext a
  simp only [Nat.zero_le,true_and,Set.mem_setOf_eq,Set.mem_range]
  exact exists_congr (fun _ => eq_comm)

end UnitDistance.JenningsCollection

namespace UnitDistance.GroupAugmentation
open JenningsCollection
variable (G : Type*) [Group G] [Finite G] (hG : IsPGroup 2 G)
variable (r : ℕ) (g : Fin r → G) (w : Fin r → ℕ)
variable (hw : ∀ i, 1 ≤ w i)
variable (hg : ∀ i, g i ∈ dimensionSubgroup (ZMod 2) G (w i))
variable (hspan : SpansActualLayers G (Fin r) g w)

include hG hw hg hspan in
/-- Arbitrarily ordered actual homogeneous differences span exactly the
augmentation power specified by their binary weights. -/
theorem binarySpan_eq_power_of_spansActualLayers (n : ℕ) :
    binarySpan (ZMod 2) G r (fun i => delta (ZMod 2) (g i)-1) w n =
      power (ZMod 2) G n := by
  rw [← orderedSpan_eq_binarySpan]
  exact orderedSpan_eq_power_of_spansActualLayers G hG (Fin r) g w hw hg hspan n

include hG hw hg hspan in
theorem span_binaryMonomial_of_spansActualLayers :
    Submodule.span (ZMod 2) (Set.range (binaryMonomial (ZMod 2) G r
      (fun i => delta (ZMod 2) (g i)-1))) = ⊤ := by
  rw [← binarySpan_zero (ZMod 2) G r _ w,
    binarySpan_eq_power_of_spansActualLayers G hG r g w hw hg hspan]
  rfl

/-- The correct number of actual homogeneous directions gives an ordinary
basis as well as the exact weighted filtration theorem above. -/
def homogeneousBinaryBasis (hcard : 2^r = Nat.card G) :
    Module.Basis (Fin r → Bool) (ZMod 2) (A (ZMod 2) G) := by
  letI : Fintype G := Fintype.ofFinite G
  apply basisOfTopLeSpanOfCardEqFinrank
    (binaryMonomial (ZMod 2) G r (fun i => delta (ZMod 2) (g i)-1))
  · exact (span_binaryMonomial_of_spansActualLayers G hG r g w hw hg hspan).ge
  · rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,hcard,
      Module.finrank_eq_card_basis (MonoidAlgebra.basis G (ZMod 2)),Nat.card_eq_fintype_card]

@[simp] theorem homogeneousBinaryBasis_apply (hcard : 2^r = Nat.card G) (c : Fin r → Bool) :
    homogeneousBinaryBasis G hG r g w hw hg hspan hcard c =
      binaryMonomial (ZMod 2) G r (fun i => delta (ZMod 2) (g i)-1) c := by
  simp [homogeneousBinaryBasis]

end UnitDistance.GroupAugmentation
