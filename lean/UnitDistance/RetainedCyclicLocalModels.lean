module

public import UnitDistance.OddLocalModels
public import UnitDistance.ExtraPrimeRadicals
public import UnitDistance.GroupAugmentationStrictness

@[expose] public section
set_option backward.privateInPublic true


/-! Actual cyclic local models at infinity and the extra primes, with strict
embeddings into the retained quadratic group for arbitrary chosen lifts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace UnitDistance.RetainedCyclic
open OddLocal RetainedQuadratic ClassTwo GroupAugmentation

theorem cyclic_pow_val (n : ℕ) [NeZero n] (x : Cyclic n) :
    x=cyclicGenerator n^x.toAdd.val := by
  apply Multiplicative.toAdd.injective
  simp [cyclicGenerator]

theorem cyclicMap_pow_val {G : Type*} [Group G] (n : ℕ) [NeZero n]
    (g : G) (hg : g^n=1) (x : Cyclic n) : cyclicMap n g hg x=g^x.toAdd.val := by
  conv_lhs => rw [cyclic_pow_val n x,map_pow,cyclicMap_generator]

theorem cyclicMap_injective {G : Type*} [Group G] (n : ℕ) [NeZero n]
    (g : G) (hg : g^n=1) (ho : orderOf g=n) : Function.Injective (cyclicMap n g hg) := by
  rw [←MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro x hx
  change cyclicMap n g hg x=1 at hx
  rw [cyclicMap_pow_val] at hx
  have hd := orderOf_dvd_of_pow_eq_one hx
  rw [ho] at hd
  have hz : x.toAdd.val=0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt x.toAdd)
  rw [cyclic_pow_val n x,hz,pow_zero]
  exact Subgroup.one_mem _

theorem cyclic_generates (n : ℕ) : Subgroup.closure ({cyclicGenerator n} : Set (Cyclic n))=⊤ := by
  apply top_unique
  intro x _
  obtain ⟨k,rfl⟩ := cyclic_eq_generator_zpow n x
  exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) k

/-- A nonzero first coordinate detects exactly the even subgroup of C4. -/
theorem cyclicFour_even (g : Q) (hg : g^4=1) (hb : g.base≠0)
    (x : Cyclic 4) (hx : (cyclicMap 4 g hg x).base=0) :
    x=1 ∨ x=cyclicGenerator 4^2 := by
  have hv := ZMod.val_lt x.toAdd
  rw [cyclicMap_pow_val] at hx
  have hn : x.toAdd.val=0 ∨ x.toAdd.val=1 ∨ x.toAdd.val=2 ∨ x.toAdd.val=3 := by omega
  rcases hn with hn | hn | hn | hn
  · left
    rw [cyclic_pow_val 4 x,hn,pow_zero]
  · exfalso
    rw [hn,pow_one] at hx
    exact hb hx
  · right
    rw [cyclic_pow_val 4 x,hn]
  · exfalso
    rw [hn,show g^3=g^2*g by group,GroupModel.mul_base,GroupModel.square_coordinates] at hx
    exact hb (by simpa using hx)

/-- Exact first and second layers for any order-four lift with nonzero genus coordinate. -/
theorem cyclicFour_strict (g : Q) (hg : g^4=1) (ho : orderOf g=4) (hb : g.base≠0) (n : ℕ) :
    (dimensionSubgroup F Q n).comap (cyclicMap 4 g hg)=dimensionSubgroup F (Cyclic 4) n := by
  have hinj := cyclicMap_injective 4 g hg ho
  have hthird : dimensionSubgroup F (Cyclic 4) 3=⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hm := map_dimensionSubgroup_le F (Cyclic 4) (cyclicMap 4 g hg) 3 ⟨x,hx,rfl⟩
    rw [GroupModel.dimensionSubgroup_three,Subgroup.mem_bot] at hm
    exact hinj (hm.trans (map_one _).symm)
  apply comap_dimensionSubgroup_eq_of_first_two_layers F (Cyclic 4) _ hthird
  · apply (layerMap_injective_iff F (Cyclic 4) _ 1).mpr
    intro x _ hx
    have hz := GroupModel.base_eq_zero_of_mem_dimension_two cocycle _ hx
    rcases cyclicFour_even g hg hb x hz with rfl | rfl
    · exact Subgroup.one_mem _
    · exact square_mem F (Cyclic 4) (n:=1) (g:=cyclicGenerator 4) (by simp)
  · apply (layerMap_injective_iff F (Cyclic 4) _ 2).mpr
    intro x _ hx
    rw [GroupModel.dimensionSubgroup_three,Subgroup.mem_bot] at hx
    have he : x=1 := hinj (hx.trans (map_one _).symm)
    simp [he]

/-- The infinite-place cyclic generator is detected in the first layer. -/
theorem cyclicTwo_trivial_of_base_zero (g : Q) (hg : g^2=1) (hb : g.base≠0)
    (x : Cyclic 2) (hx : (cyclicMap 2 g hg x).base=0) : x=1 := by
  have hv := ZMod.val_lt x.toAdd
  rw [cyclicMap_pow_val] at hx
  have hn : x.toAdd.val=0 ∨ x.toAdd.val=1 := by omega
  rcases hn with hn | hn
  · rw [cyclic_pow_val 2 x,hn,pow_zero]
  · exfalso
    rw [hn,pow_one] at hx
    exact hb hx

theorem cyclicTwo_injective (g : Q) (hg : g^2=1) (hb : g.base≠0) :
    Function.Injective (cyclicMap 2 g hg) := by
  rw [←MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro x hx
  exact cyclicTwo_trivial_of_base_zero g hg hb x (congrArg GroupModel.base hx)

theorem cyclicTwo_dimension_two (g : Q) (hg : g^2=1) (hb : g.base≠0) :
    dimensionSubgroup F (Cyclic 2) 2=⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hm := map_dimensionSubgroup_le F (Cyclic 2) (cyclicMap 2 g hg) 2 ⟨x,hx,rfl⟩
  exact cyclicTwo_trivial_of_base_zero g hg hb x
    (GroupModel.base_eq_zero_of_mem_dimension_two cocycle _ hm)

theorem cyclicTwo_strict (g : Q) (hg : g^2=1) (hb : g.base≠0) (n : ℕ) :
    (dimensionSubgroup F Q n).comap (cyclicMap 2 g hg)=dimensionSubgroup F (Cyclic 2) n := by
  have hinj := cyclicTwo_injective g hg hb
  have hthird : dimensionSubgroup F (Cyclic 2) 3=⊥ :=
    le_bot_iff.mp ((dimensionSubgroup_antitone F (Cyclic 2) (by omega : 2≤3)).trans
      (cyclicTwo_dimension_two g hg hb).le)
  apply comap_dimensionSubgroup_eq_of_first_two_layers F (Cyclic 2) _ hthird
  · apply (layerMap_injective_iff F (Cyclic 2) _ 1).mpr
    intro x _ hx
    have he := cyclicTwo_trivial_of_base_zero g hg hb x
      (GroupModel.base_eq_zero_of_mem_dimension_two cocycle _ hx)
    simp [he]
  · apply (layerMap_injective_iff F (Cyclic 2) _ 2).mpr
    intro x _ hx
    rw [GroupModel.dimensionSubgroup_three,Subgroup.mem_bot] at hx
    have he : x=1 := hinj (hx.trans (map_one _).symm)
    simp [he]

def infinityElement : Q := ⟨Pi.single 0 1,0⟩
theorem infinityElement_square : infinityElement^2=1 := by
  apply GroupModel.ext <;> funext i <;> fin_cases i <;> decide +kernel
theorem infinityElement_base_ne_zero : infinityElement.base≠0 := by decide +kernel

def extraElement (i : Fin 5) : Q := ⟨ExtraPrime.vector i,0⟩
theorem extraElement_order (i : Fin 5) : orderOf (extraElement i)=4 := ExtraPrime.retained_order i _ rfl
theorem extraElement_fourth (i : Fin 5) : extraElement i^4=1 := by
  rw [←extraElement_order i,pow_orderOf_eq_one]

/-- C2 and C4 with their actual strict retained embeddings. -/
def infinityMap : Cyclic 2 →* Q := cyclicMap 2 infinityElement infinityElement_square
def extraMap (i : Fin 5) : Cyclic 4 →* Q := cyclicMap 4 (extraElement i) (extraElement_fourth i)

theorem infinityMap_strict (n : ℕ) : (dimensionSubgroup F Q n).comap infinityMap=
    dimensionSubgroup F (Cyclic 2) n :=
  cyclicTwo_strict infinityElement infinityElement_square infinityElement_base_ne_zero n

theorem extraMap_strict (i : Fin 5) (n : ℕ) : (dimensionSubgroup F Q n).comap (extraMap i)=
    dimensionSubgroup F (Cyclic 4) n :=
  cyclicFour_strict _ (extraElement_fourth i) (extraElement_order i) (ExtraPrime.vector_ne_zero i) n

theorem cyclicFour_dimension_two_le : dimensionSubgroup F (Cyclic 4) 2≤
    Subgroup.closure ({cyclicGenerator 4^2} : Set (Cyclic 4)) := by
  intro x hx
  have hm := map_dimensionSubgroup_le F (Cyclic 4) (extraMap 0) 2 ⟨x,hx,rfl⟩
  have hb := GroupModel.base_eq_zero_of_mem_dimension_two cocycle _ hm
  rcases cyclicFour_even _ (extraElement_fourth 0) (ExtraPrime.vector_ne_zero 0) x hb with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (by simp)

theorem cyclicFour_dimension_three : dimensionSubgroup F (Cyclic 4) 3=⊥ := by
  rw [←extraMap_strict 0,GroupModel.dimensionSubgroup_three]
  change (extraMap 0).ker=⊥
  rw [MonoidHom.ker_eq_bot_iff]
  exact cyclicMap_injective 4 _ (extraElement_fourth 0) (extraElement_order 0)

end UnitDistance.RetainedCyclic
