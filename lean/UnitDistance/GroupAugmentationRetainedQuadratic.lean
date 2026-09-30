module

public import UnitDistance.GroupAugmentationClassTwo
public import UnitDistance.GroupAugmentationGeneratorHom
public import UnitDistance.GroupAugmentationDyadic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The concrete retained quadratic group

The group is defined by explicit bilinear multiplication on F₂⁷ × F₂¹².
The coefficients are the exact reduction of the manuscript's sixteen
quadratic relations. Its construction is independent of any claimed global
Galois group. The arithmetic map onto this finite object remains separate.
-/

open scoped BigOperators
namespace UnitDistance.RetainedQuadratic
open GroupAugmentation ClassTwo
abbrev F := ZMod 2
abbrev V := Fin 7 → F
abbrev W := Fin 12 → F

def binaryVector (n mask : ℕ) : Fin n → F := fun i => if mask.testBit i.val then 1 else 0

/-- Coordinates of the 28 free quadratic basis vectors after eliminating
exactly the sixteen displayed relation rows. -/
def quadraticColumns : Fin 28 → ℕ :=
  ![0,0,0,0,0,0,0,1,2,4,8,16,32,64,128,256,321,385,512,1024,578,2048,2249,468,2633,1624,3265,1801]

/-- Lower triangular multiplication tensor in the twelve retained central
coordinates, using the manuscript's ordered seven genus generators. -/
def cocycleMasks : Fin 7 → Fin 7 → ℕ :=
  ![![0,0,0,0,0,0,0],![1,0,0,0,0,0,0],![2,64,0,0,0,0,0],
    ![4,128,512,0,0,0,0],![8,256,1024,2249,0,0,0],
    ![16,321,578,468,1624,0,0],![32,385,2048,2633,3265,1801,0]]

/-- This bilinear law, rather than any asserted ranks, defines the group. -/
def cocycle : V →ₗ[F] V →ₗ[F] W where
  toFun v :=
    { toFun := fun w => ∑ i, ∑ j, (v i*w j) • binaryVector 12 (cocycleMasks i j)
      map_add' w w' := by
        simp only [Pi.add_apply,mul_add,add_smul,Finset.sum_add_distrib]
      map_smul' r w := by
        simp only [Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]
        simp only [RingHom.id_apply,mul_left_comm] }
  map_add' v v' := by
    apply LinearMap.ext
    intro w
    change (∑ i, ∑ j, ((v i+v' i)*w j) • binaryVector 12 (cocycleMasks i j)) = _
    simp only [add_mul,add_smul,Finset.sum_add_distrib]
    rfl
  map_smul' r v := by
    apply LinearMap.ext
    intro w
    change (∑ i, ∑ j, ((r*v i)*w j) • binaryVector 12 (cocycleMasks i j)) =
      r • (∑ i, ∑ j, (v i*w j) • binaryVector 12 (cocycleMasks i j))
    simp only [Finset.smul_sum,smul_smul,mul_assoc]

abbrev Q := GroupModel cocycle

/-- The order follows from the actual independent coordinate types. -/
theorem card_Q : Nat.card Q = 2^19 := by
  rw [Nat.card_congr (GroupModel.equivProd cocycle),Nat.card_prod]
  simp only [V,W,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  norm_num

theorem Q_isTwoGroup : IsPGroup 2 Q := GroupModel.isTwoGroup cocycle

def x : Q := ⟨binaryVector 7 2,0⟩
def y : Q := ⟨binaryVector 7 53,0⟩
def z : Q := ⟨binaryVector 7 89,0⟩
def w : Q := y⁻¹*z⁻¹*y*z

/-- Explicit coordinates of the local normal-form embedding, indexed by
`D.index`; the Cayley-edge certificate below checks the actual group law. -/
def dyadicBaseMasks : Fin 32 → ℕ :=
  ![0,0,89,89,0,0,89,89,53,53,108,108,53,53,108,108,2,2,91,91,2,2,91,91,55,55,110,110,55,55,110,110]

def dyadicCentralMasks : Fin 32 → ℕ :=
  ![0,2747,0,2747,3693,1238,3693,1238,0,2747,3935,1508,3693,1238,306,2953,0,2747,1,2746,3693,1238,3692,1239,1,2746,3935,1508,3692,1239,306,2953]

def dyadicMapFn (g : Dyadic.D) : Q :=
  ⟨binaryVector 7 (dyadicBaseMasks (Dyadic.D.index g)),
    binaryVector 12 (dyadicCentralMasks (Dyadic.D.index g))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem dyadicMapFn_one : dyadicMapFn 1 = 1 := by
  have hindex : Dyadic.D.index 1 = 0 := by decide
  apply GroupModel.ext <;> funext i <;>
    simp [dyadicMapFn,hindex,dyadicBaseMasks,dyadicCentralMasks,binaryVector]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Ninety-six actual Cayley-edge identities certify the homomorphism. -/
theorem dyadicMapFn_step_coordinates : ∀ (g : Dyadic.D) (i : Fin 3),
    (∀ k, (dyadicMapFn (g*Dyadic.Filtration.gen i)).base k =
      (dyadicMapFn g*dyadicMapFn (Dyadic.Filtration.gen i)).base k) ∧
    (∀ k, (dyadicMapFn (g*Dyadic.Filtration.gen i)).central k =
      (dyadicMapFn g*dyadicMapFn (Dyadic.Filtration.gen i)).central k) := by
  decide +kernel

theorem dyadicMapFn_step (g : Dyadic.D) (i : Fin 3) :
    dyadicMapFn (g*Dyadic.Filtration.gen i) = dyadicMapFn g*dyadicMapFn (Dyadic.Filtration.gen i) := by
  apply GroupModel.ext
  · exact funext (dyadicMapFn_step_coordinates g i).1
  · exact funext (dyadicMapFn_step_coordinates g i).2

/-- The concrete local homomorphism into the retained quadratic group. -/
def dyadicMap : Dyadic.D →* Q :=
  homOfRightGenerators dyadicMapFn dyadicMapFn_one Dyadic.Filtration.gen
    dyadic_generators dyadicMapFn_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem dyadicMap_kernel_certificate : ∀ g : Dyadic.D,
    (dyadicMapFn g).base 1 = 0 → (dyadicMapFn g).base 2 = 0 →
    (dyadicMapFn g).base 3 = 0 → (dyadicMapFn g).central 1 = 0 →
    (dyadicMapFn g).central 2 = 0 → g = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem dyadicMap_base_certificate : ∀ g : Dyadic.D,
    ((dyadicMapFn g).base 1 = 0 ∧ (dyadicMapFn g).base 2 = 0 ∧
      (dyadicMapFn g).base 3 = 0) ↔ g.a = 0 ∧ g.b = 0 ∧ Dyadic.parity g.c = 0 := by
  decide +kernel

theorem dyadicMap_injective : Function.Injective dyadicMap := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro g hg
  have he : dyadicMapFn g = 1 := hg
  apply dyadicMap_kernel_certificate g
  all_goals rw [he]; rfl

/-- The actual first augmentation layer of the dyadic group embeds. -/
theorem dyadicMap_first_layer : Function.Injective (layerMap F Dyadic.D dyadicMap 1) := by
  apply (layerMap_injective_iff F Dyadic.D dyadicMap 1).mpr
  intro g _ hg
  have hb := GroupModel.base_eq_zero_of_mem_dimension_two cocycle (dyadicMap g) hg
  rw [dyadic_dimensionSubgroup,Dyadic.AlgebraD.mem_dimensionSubgroup_two]
  apply (dyadicMap_base_certificate g).mp
  change (dyadicMap g).base 1 = 0 ∧ (dyadicMap g).base 2 = 0 ∧ (dyadicMap g).base 3 = 0
  simp [hb]

/-- The actual second augmentation layer also embeds, because the actual
third subgroup of the concrete ambient model is trivial. -/
theorem dyadicMap_second_layer : Function.Injective (layerMap F Dyadic.D dyadicMap 2) := by
  apply (layerMap_injective_iff F Dyadic.D dyadicMap 2).mpr
  intro g _ hg
  rw [GroupModel.dimensionSubgroup_three,Subgroup.mem_bot] at hg
  have hg1 : g = 1 := dyadicMap_injective (hg.trans (map_one dyadicMap).symm)
  simp [hg1]

/-- All actual augmentation layers are compatible for this explicit local
embedding. No ambient layer-injection assumption is used. -/
theorem dyadicMap_comap_dimensionSubgroup (n : ℕ) :
    (dimensionSubgroup F Q n).comap dyadicMap = Dyadic.AlgebraD.dimensionSubgroup n :=
  dyadic_comap_dimensionSubgroup dyadicMap dyadicMap_first_layer dyadicMap_second_layer n

end UnitDistance.RetainedQuadratic
