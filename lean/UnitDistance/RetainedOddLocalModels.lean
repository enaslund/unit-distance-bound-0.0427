module

public import UnitDistance.OddLocalModels
public import UnitDistance.RetainedQuadraticCutWords
public import UnitDistance.RetainedDyadicLifts
public import UnitDistance.GroupAugmentationStrictness
public import Mathlib.Algebra.Module.Pi

@[expose] public section
set_option backward.privateInPublic true


/-! The five odd local groups embed in the retained arithmetic model.
Their actual augmentation filtrations are strict in every degree. -/
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace UnitDistance.RetainedQuadratic
open ClassTwo GroupAugmentation
local instance : AddCommGroup F := Ring.toAddCommGroup
local instance : Module F F := Semiring.toModule
local instance : AddCommGroup V := Pi.addCommGroup
local instance : AddCommGroup W := Pi.addCommGroup
local instance : Module F V := Pi.Function.module (Fin 7) F F
local instance : Module F W := Pi.Function.module (Fin 12) F F
attribute [local irreducible] cocycle

def oddInertia (i : Fin 5) : Q := ⟨Cut.inertiaVector i,0⟩
def oddFrobenius (i : Fin 5) : Q := ⟨Cut.frobeniusVector i,0⟩

theorem odd_relations_coordinates : ∀ i : Fin 5,
    ((∀ k,(oddInertia i^2).base k=0) ∧ (∀ k,(oddInertia i^2).central k=0)) ∧
    ((∀ k,(oddFrobenius i^OddLocal.residueDegree i).base k=0) ∧
      (∀ k,(oddFrobenius i^OddLocal.residueDegree i).central k=0)) ∧
    ((∀ k,(oddInertia i*oddFrobenius i).base k=(oddFrobenius i*oddInertia i).base k) ∧
      (∀ k,(oddInertia i*oddFrobenius i).central k=(oddFrobenius i*oddInertia i).central k)) := by
  decide +kernel

theorem odd_relations (i : Fin 5) :
    oddInertia i^2=1 ∧ oddFrobenius i^OddLocal.residueDegree i=1 ∧
      Commute (oddInertia i) (oddFrobenius i) := by
  refine ⟨GroupModel.ext (funext (odd_relations_coordinates i).1.1)
    (funext (odd_relations_coordinates i).1.2),
    GroupModel.ext (funext (odd_relations_coordinates i).2.1.1)
    (funext (odd_relations_coordinates i).2.1.2),?_⟩
  exact GroupModel.ext (funext (odd_relations_coordinates i).2.2.1)
    (funext (odd_relations_coordinates i).2.2.2)

def oddMap (i : Fin 5) : OddLocal.D i →* Q :=
  OddLocal.map i (oddInertia i) (oddFrobenius i)
    (odd_relations i).1 (odd_relations i).2.1 (odd_relations i).2.2

@[simp] theorem oddMap_inertia (i : Fin 5) : oddMap i (OddLocal.inertia i)=oddInertia i :=
  OddLocal.map_inertia ..
@[simp] theorem oddMap_frobenius (i : Fin 5) : oddMap i (OddLocal.frobenius i)=oddFrobenius i :=
  OddLocal.map_frobenius ..

def oddMapFn (i : Fin 5) (g : OddLocal.D i) : Q :=
  oddInertia i^g.1.toAdd.val*oddFrobenius i^g.2.toAdd.val

theorem oddMap_eq_fn (i : Fin 5) (g : OddLocal.D i) : oddMap i g=oddMapFn i g := by
  have hcyc (n : ℕ) [NeZero n] (x : OddLocal.Cyclic n) :
      x=OddLocal.cyclicGenerator n^x.toAdd.val := by
    apply Multiplicative.toAdd.injective
    simp [OddLocal.cyclicGenerator]
  have hg : g=OddLocal.inertia i^g.1.toAdd.val*OddLocal.frobenius i^g.2.toAdd.val := by
    ext <;> simp [OddLocal.inertia,OddLocal.frobenius,←hcyc]
  conv_lhs => rw [hg,map_mul,map_pow,map_pow,oddMap_inertia,oddMap_frobenius]
  rfl

theorem oddMap_kernel_certificate : ∀ (i : Fin 5) (g : OddLocal.D i),
    (∀ k,(oddMapFn i g).base k=0) → (∀ k,(oddMapFn i g).central k=0) → g=1 := by decide +kernel

theorem oddMap_first_layer_certificate : ∀ (i : Fin 5) (g : OddLocal.D i),
    (∀ k,(oddMapFn i g).base k=0) → g=1 ∨ g=OddLocal.frobenius i^2 := by decide +kernel

theorem oddMap_injective (i : Fin 5) : Function.Injective (oddMap i) := by
  rw [←MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro g hg
  have he : oddMapFn i g=1 := (oddMap_eq_fn i g).symm.trans hg
  apply oddMap_kernel_certificate i g <;> intro k <;> rw [he] <;> rfl

theorem odd_dimensionSubgroup_three (i : Fin 5) : dimensionSubgroup F (OddLocal.D i) 3=⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have hm := map_dimensionSubgroup_le F (OddLocal.D i) (oddMap i) 3 ⟨g,hg,rfl⟩
  rw [GroupModel.dimensionSubgroup_three,Subgroup.mem_bot] at hm
  exact (oddMap_injective i) (hm.trans (map_one _).symm)

theorem oddMap_first_layer (i : Fin 5) :
    Function.Injective (layerMap F (OddLocal.D i) (oddMap i) 1) := by
  apply (layerMap_injective_iff F (OddLocal.D i) (oddMap i) 1).mpr
  intro g _ hg
  have hb := GroupModel.base_eq_zero_of_mem_dimension_two cocycle (oddMap i g) hg
  rw [oddMap_eq_fn] at hb
  rcases oddMap_first_layer_certificate i g (fun k ↦ congrFun hb k) with rfl | rfl
  · exact Subgroup.one_mem _
  · exact square_mem F (OddLocal.D i) (n := 1) (g := OddLocal.frobenius i) (by simp)

theorem oddMap_second_layer (i : Fin 5) :
    Function.Injective (layerMap F (OddLocal.D i) (oddMap i) 2) := by
  apply (layerMap_injective_iff F (OddLocal.D i) (oddMap i) 2).mpr
  intro g _ hg
  rw [GroupModel.dimensionSubgroup_three,Subgroup.mem_bot] at hg
  have he : g=1 := (oddMap_injective i) (hg.trans (map_one _).symm)
  simp [he]

theorem oddMap_comap_dimensionSubgroup (i : Fin 5) (n : ℕ) :
    (dimensionSubgroup F Q n).comap (oddMap i)=dimensionSubgroup F (OddLocal.D i) n :=
  comap_dimensionSubgroup_eq_of_first_two_layers F (OddLocal.D i) (oddMap i)
    (odd_dimensionSubgroup_three i) (oddMap_first_layer i) (oddMap_second_layer i) n

def oddUnitCoordinate (i : Fin 5) : Fin 7 := ![0,1,0,0,1] i

def oddAdjustment (i : Fin 5) (a b : W) : V →ₗ[F] W where
  toFun v := v ⟨i.val+2,by omega⟩ • a+v (oddUnitCoordinate i) • b
  map_add' v w := by simp only [Pi.add_apply,add_smul]; abel
  map_smul' r v := by simp only [Pi.smul_apply,smul_eq_mul,smul_smul,RingHom.id_apply,smul_add]

theorem odd_dual_coordinates : ∀ i : Fin 5,
    Cut.inertiaVector i ⟨i.val+2,by omega⟩=1 ∧
    Cut.inertiaVector i (oddUnitCoordinate i)=0 ∧
    Cut.frobeniusVector i ⟨i.val+2,by omega⟩=0 ∧
    Cut.frobeniusVector i (oddUnitCoordinate i)=1 := by decide +kernel

@[simp] theorem oddAdjustment_inertia (i : Fin 5) (a b : W) :
    oddAdjustment i a b (Cut.inertiaVector i)=a := by
  change Cut.inertiaVector i _ • a+Cut.inertiaVector i _ • b=a
  rw [(odd_dual_coordinates i).1,(odd_dual_coordinates i).2.1]
  simp

@[simp] theorem oddAdjustment_frobenius (i : Fin 5) (a b : W) :
    oddAdjustment i a b (Cut.frobeniusVector i)=b := by
  change Cut.frobeniusVector i _ • a+Cut.frobeniusVector i _ • b=b
  rw [(odd_dual_coordinates i).2.2.1,(odd_dual_coordinates i).2.2.2]
  simp

def oddMapOfLifts (i : Fin 5) (a b : Q) : OddLocal.D i →* Q :=
  (GroupModel.centralShear cocycle (oddAdjustment i a.central b.central)).toMonoidHom.comp (oddMap i)

theorem oddMapOfLifts_injective (i : Fin 5) (a b : Q) :
    Function.Injective (oddMapOfLifts i a b) :=
  (GroupModel.centralShear cocycle _).injective.comp (oddMap_injective i)

@[simp] theorem oddMapOfLifts_inertia (i : Fin 5) (a b : Q) (ha : a.base=Cut.inertiaVector i) :
    oddMapOfLifts i a b (OddLocal.inertia i)=a := by
  change GroupModel.centralShear cocycle _ (oddMap i (OddLocal.inertia i))=a
  rw [oddMap_inertia]
  apply GroupModel.ext
  · exact ha.symm
  · change 0+oddAdjustment i a.central b.central (Cut.inertiaVector i)=a.central
    simp

@[simp] theorem oddMapOfLifts_frobenius (i : Fin 5) (a b : Q) (hb : b.base=Cut.frobeniusVector i) :
    oddMapOfLifts i a b (OddLocal.frobenius i)=b := by
  change GroupModel.centralShear cocycle _ (oddMap i (OddLocal.frobenius i))=b
  rw [oddMap_frobenius]
  apply GroupModel.ext
  · exact hb.symm
  · change 0+oddAdjustment i a.central b.central (Cut.frobeniusVector i)=b.central
    simp

theorem oddMapOfLifts_comap_dimensionSubgroup (i : Fin 5) (a b : Q) (n : ℕ) :
    (dimensionSubgroup F Q n).comap (oddMapOfLifts i a b)=dimensionSubgroup F (OddLocal.D i) n := by
  let e := GroupModel.centralShear cocycle (oddAdjustment i a.central b.central)
  have he : (dimensionSubgroup F Q n).comap e.toMonoidHom=dimensionSubgroup F Q n := by
    ext g
    change e g∈dimensionSubgroup F Q n ↔ g∈dimensionSubgroup F Q n
    constructor
    · intro h
      have hh := map_dimensionSubgroup_le F Q e.symm.toMonoidHom n ⟨e g,h,rfl⟩
      simpa using hh
    · intro h
      exact map_dimensionSubgroup_le F Q e.toMonoidHom n ⟨g,h,rfl⟩
  change (dimensionSubgroup F Q n).comap (e.toMonoidHom.comp (oddMap i))=_
  rw [←Subgroup.comap_comap,he]
  exact oddMap_comap_dimensionSubgroup i n

end UnitDistance.RetainedQuadratic
