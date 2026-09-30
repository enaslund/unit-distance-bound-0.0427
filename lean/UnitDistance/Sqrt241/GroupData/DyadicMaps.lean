module

public import UnitDistance.Sqrt241.GroupData.LocalModels
public import UnitDistance.GroupAugmentationGeneratorHom
public import UnitDistance.GroupAugmentationDyadic
public import UnitDistance.RetainedDyadicLifts

@[expose] public section
set_option backward.privateInPublic true


/-!
# The order-32 dyadic group inside `Q_B` at both dyadic places

For `P = 0, 1` (`𝔭₁, 𝔭₂`) an explicit normal-form map `Dyadic.D → Q_B`
sending `x, y, z` to `(x_P, 0), (y_P, 0), (z_P, 0)` is certified to be a
homomorphism by 192 Cayley-edge identities and to be injective; its kernel on
elementary coordinates is `D₂(D)`, so all augmentation layers inject. Three
linear characters dual to `(x_P, y_P, z_P)` are given (for `P = 0`:
`v₁+v₂, v₁, v₅`). A central shear adapts the map to arbitrary lifts with the
same elementary vectors (`dyadicMapOfLifts`), keeping all these properties.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.Retained
open ClassTwo GroupData GroupAugmentation

/-- Explicit normal-form images, indexed by `D.index`. -/
def dyadicMapFn (P : Fin 2) (g : Dyadic.D) : Q :=
  ⟨bits 8 (dyadicBaseMasks P (Dyadic.D.index g)),bits 15 (dyadicCentralMasks P (Dyadic.D.index g))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem dyadicMapFn_one (P : Fin 2) : dyadicMapFn P 1 = 1 := by
  have hindex : Dyadic.D.index 1 = 0 := by decide
  apply GroupModel.ext <;> funext i <;> revert P i <;>
    simp only [dyadicMapFn,hindex] <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Cayley-edge identities at `𝔭₁`. Checked one generator (base part) and one
generator and central coordinate at a time, each over all 32 elements of `D`, so that
every kernel reduction stays small. -/
theorem dyadicMapFn_step_coordinates_zero : ∀ (g : Dyadic.D) (i : Fin 3),
    (∀ k, (dyadicMapFn 0 (g*Dyadic.Filtration.gen i)).base k =
      (dyadicMapFn 0 g*dyadicMapFn 0 (Dyadic.Filtration.gen i)).base k) ∧
    (∀ k, (dyadicMapFn 0 (g*Dyadic.Filtration.gen i)).central k =
      (dyadicMapFn 0 g*dyadicMapFn 0 (Dyadic.Filtration.gen i)).central k) := by
  have hbase : ∀ (i : Fin 3) (g : Dyadic.D) (k : Fin 8),
      (dyadicMapFn 0 (g*Dyadic.Filtration.gen i)).base k =
        (dyadicMapFn 0 g*dyadicMapFn 0 (Dyadic.Filtration.gen i)).base k := by
    intro i
    fin_cases i <;> decide +kernel
  have hcentral : ∀ (i : Fin 3) (k : Fin 15) (g : Dyadic.D),
      (dyadicMapFn 0 (g*Dyadic.Filtration.gen i)).central k =
        (dyadicMapFn 0 g*dyadicMapFn 0 (Dyadic.Filtration.gen i)).central k := by
    intro i k
    fin_cases i <;> fin_cases k <;> decide +kernel
  exact fun g i => ⟨hbase i g, fun k => hcentral i k g⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Cayley-edge identities at `𝔭₂`. Checked one generator (base part) and one
generator and central coordinate at a time, each over all 32 elements of `D`, so that
every kernel reduction stays small. -/
theorem dyadicMapFn_step_coordinates_one : ∀ (g : Dyadic.D) (i : Fin 3),
    (∀ k, (dyadicMapFn 1 (g*Dyadic.Filtration.gen i)).base k =
      (dyadicMapFn 1 g*dyadicMapFn 1 (Dyadic.Filtration.gen i)).base k) ∧
    (∀ k, (dyadicMapFn 1 (g*Dyadic.Filtration.gen i)).central k =
      (dyadicMapFn 1 g*dyadicMapFn 1 (Dyadic.Filtration.gen i)).central k) := by
  have hbase : ∀ (i : Fin 3) (g : Dyadic.D) (k : Fin 8),
      (dyadicMapFn 1 (g*Dyadic.Filtration.gen i)).base k =
        (dyadicMapFn 1 g*dyadicMapFn 1 (Dyadic.Filtration.gen i)).base k := by
    intro i
    fin_cases i <;> decide +kernel
  have hcentral : ∀ (i : Fin 3) (k : Fin 15) (g : Dyadic.D),
      (dyadicMapFn 1 (g*Dyadic.Filtration.gen i)).central k =
        (dyadicMapFn 1 g*dyadicMapFn 1 (Dyadic.Filtration.gen i)).central k := by
    intro i k
    fin_cases i <;> fin_cases k <;> decide +kernel
  exact fun g i => ⟨hbase i g, fun k => hcentral i k g⟩

theorem dyadicMapFn_step (P : Fin 2) (g : Dyadic.D) (i : Fin 3) :
    dyadicMapFn P (g*Dyadic.Filtration.gen i) =
      dyadicMapFn P g*dyadicMapFn P (Dyadic.Filtration.gen i) := by
  fin_cases P
  · exact GroupModel.ext (funext (dyadicMapFn_step_coordinates_zero g i).1)
      (funext (dyadicMapFn_step_coordinates_zero g i).2)
  · exact GroupModel.ext (funext (dyadicMapFn_step_coordinates_one g i).1)
      (funext (dyadicMapFn_step_coordinates_one g i).2)

/-- The canonical embedding of `D` at `𝔭_P`. -/
def dyadicMap (P : Fin 2) : Dyadic.D →* Q :=
  homOfRightGenerators (dyadicMapFn P) (dyadicMapFn_one P) Dyadic.Filtration.gen
    dyadic_generators (dyadicMapFn_step P)

theorem dyadicMap_apply (P : Fin 2) (g : Dyadic.D) : dyadicMap P g = dyadicMapFn P g := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem dyadicMap_kernel_certificate : ∀ (P : Fin 2) (g : Dyadic.D),
    (∀ k, (dyadicMapFn P g).base k = 0) → (∀ k, (dyadicMapFn P g).central k = 0) → g = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem dyadicMap_base_certificate : ∀ (P : Fin 2) (g : Dyadic.D),
    (∀ k, (dyadicMapFn P g).base k = 0) → g.a = 0 ∧ g.b = 0 ∧ Dyadic.parity g.c = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem dyadicMap_generators_certificate : ∀ (P : Fin 2) (k : Fin 8) (l : Fin 15),
    (dyadicMapFn P Dyadic.D.x).base k = dyadicXVector P k ∧
    (dyadicMapFn P Dyadic.D.y).base k = dyadicYVector P k ∧
    (dyadicMapFn P Dyadic.D.z).base k = dyadicZVector P k ∧
    (dyadicMapFn P Dyadic.D.x).central l = 0 ∧ (dyadicMapFn P Dyadic.D.y).central l = 0 ∧
    (dyadicMapFn P Dyadic.D.z).central l = 0 := by
  decide +kernel

theorem dyadicMap_x (P : Fin 2) : dyadicMap P Dyadic.D.x = ⟨dyadicXVector P,0⟩ :=
  GroupModel.ext (funext fun k => (dyadicMap_generators_certificate P k 0).1)
    (funext fun l => (dyadicMap_generators_certificate P 0 l).2.2.2.1)
theorem dyadicMap_y (P : Fin 2) : dyadicMap P Dyadic.D.y = ⟨dyadicYVector P,0⟩ :=
  GroupModel.ext (funext fun k => (dyadicMap_generators_certificate P k 0).2.1)
    (funext fun l => (dyadicMap_generators_certificate P 0 l).2.2.2.2.1)
theorem dyadicMap_z (P : Fin 2) : dyadicMap P Dyadic.D.z = ⟨dyadicZVector P,0⟩ :=
  GroupModel.ext (funext fun k => (dyadicMap_generators_certificate P k 0).2.2.1)
    (funext fun l => (dyadicMap_generators_certificate P 0 l).2.2.2.2.2)

theorem dyadicMap_injective (P : Fin 2) : Function.Injective (dyadicMap P) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro g hg
  have he : dyadicMapFn P g = 1 := hg
  apply dyadicMap_kernel_certificate P g
  all_goals intro k; rw [he]; rfl

theorem dyadicMap_first_layer (P : Fin 2) :
    Function.Injective (layerMap F Dyadic.D (dyadicMap P) 1) := by
  apply (layerMap_injective_iff F Dyadic.D (dyadicMap P) 1).mpr
  intro g _ hg
  have hb := GroupModel.base_eq_zero_of_mem_dimension_two cocycle (dyadicMap P g) hg
  rw [dyadic_dimensionSubgroup,Dyadic.AlgebraD.mem_dimensionSubgroup_two]
  apply dyadicMap_base_certificate P g
  intro k
  change (dyadicMap P g).base k = 0
  rw [hb]
  rfl

theorem dyadicMap_second_layer (P : Fin 2) :
    Function.Injective (layerMap F Dyadic.D (dyadicMap P) 2) := by
  apply (layerMap_injective_iff F Dyadic.D (dyadicMap P) 2).mpr
  intro g _ hg
  rw [GroupModel.dimensionSubgroup_three,Subgroup.mem_bot] at hg
  have hg1 : g = 1 := dyadicMap_injective P (hg.trans (map_one _).symm)
  simp [hg1]

theorem dyadicMap_comap_dimensionSubgroup (P : Fin 2) (n : ℕ) :
    (dimensionSubgroup F Q n).comap (dyadicMap P) = Dyadic.AlgebraD.dimensionSubgroup n :=
  dyadic_comap_dimensionSubgroup (dyadicMap P) (dyadicMap_first_layer P)
    (dyadicMap_second_layer P) n

/-! ### Dual characters -/

/-- The linear character `q ↦ χ(q.base)` given by a mask. -/
def baseCharacter (mask : ℕ) : Q →* Multiplicative F where
  toFun q := Multiplicative.ofAdd (maskFunctional 8 mask q.base)
  map_one' := by
    change Multiplicative.ofAdd (maskFunctional 8 mask 0) = 1
    rw [map_zero]
    rfl
  map_mul' g h := by
    change Multiplicative.ofAdd (maskFunctional 8 mask (g.base+h.base)) = _
    rw [map_add]
    rfl

/-- Characters dual to the dyadic generators `(x_P, y_P, z_P)`. -/
def dyadicCharacter (P : Fin 2) (k : Fin 3) : Q →* Multiplicative F :=
  baseCharacter (dyadicCharacterMasks P k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem dyadicCharacter_vector_certificate : ∀ (P : Fin 2) (j k : Fin 3),
    maskFunctional 8 (dyadicCharacterMasks P k) (![dyadicXVector P,dyadicYVector P,dyadicZVector P] j) =
      (Pi.single j (1 : F) : Fin 3 → F) k := by
  decide +kernel

theorem dyadicCharacter_certificate (P : Fin 2) (j k : Fin 3) :
    (dyadicCharacter P k (dyadicMap P (Dyadic.Filtration.gen j))).toAdd =
      (Pi.single j (1 : F) : Fin 3 → F) k := by
  have hgen : (dyadicMap P (Dyadic.Filtration.gen j)).base =
      ![dyadicXVector P,dyadicYVector P,dyadicZVector P] j := by
    fin_cases j
    · exact congrArg GroupModel.base (dyadicMap_x P)
    · exact congrArg GroupModel.base (dyadicMap_y P)
    · exact congrArg GroupModel.base (dyadicMap_z P)
  change maskFunctional 8 (dyadicCharacterMasks P k) (dyadicMap P (Dyadic.Filtration.gen j)).base = _
  rw [hgen]
  exact dyadicCharacter_vector_certificate P j k

/-! ### Adaptation to arbitrary lifts -/

/-- The linear map with prescribed values `a, b, c` on `x_P, y_P, z_P`. -/
def dyadicAdjustment (P : Fin 2) (a b c : W) : V →ₗ[F] W where
  toFun v := maskFunctional 8 (dyadicCharacterMasks P 0) v • a +
    maskFunctional 8 (dyadicCharacterMasks P 1) v • b +
    maskFunctional 8 (dyadicCharacterMasks P 2) v • c
  map_add' v w := by simp only [map_add,add_smul]; abel
  map_smul' r v := by simp only [map_smul,smul_eq_mul,mul_smul,RingHom.id_apply,smul_add]

theorem dyadicAdjustment_apply (P : Fin 2) (a b c : W) (j : Fin 3) :
    dyadicAdjustment P a b c (![dyadicXVector P,dyadicYVector P,dyadicZVector P] j) =
      ![a,b,c] j := by
  change maskFunctional 8 (dyadicCharacterMasks P 0) _ • a +
    maskFunctional 8 (dyadicCharacterMasks P 1) _ • b +
    maskFunctional 8 (dyadicCharacterMasks P 2) _ • c = _
  rw [dyadicCharacter_vector_certificate,dyadicCharacter_vector_certificate,
    dyadicCharacter_vector_certificate]
  fin_cases j <;> simp

/-- The canonical embedding adjusted to lifts `a, b, c` of `x_P, y_P, z_P`. -/
def dyadicMapOfLifts (P : Fin 2) (a b c : Q) : Dyadic.D →* Q :=
  (GroupModel.centralShear cocycle
    (dyadicAdjustment P a.central b.central c.central)).toMonoidHom.comp (dyadicMap P)

theorem dyadicMapOfLifts_injective (P : Fin 2) (a b c : Q) :
    Function.Injective (dyadicMapOfLifts P a b c) :=
  (GroupModel.centralShear cocycle _).injective.comp (dyadicMap_injective P)

theorem dyadicMapOfLifts_gen (P : Fin 2) (a b c : Q) (j : Fin 3)
    (hbase : (![a,b,c] j).base = ![dyadicXVector P,dyadicYVector P,dyadicZVector P] j) :
    dyadicMapOfLifts P a b c (Dyadic.Filtration.gen j) = ![a,b,c] j := by
  have hcan : dyadicMap P (Dyadic.Filtration.gen j) =
      ⟨![dyadicXVector P,dyadicYVector P,dyadicZVector P] j,0⟩ := by
    fin_cases j
    · exact dyadicMap_x P
    · exact dyadicMap_y P
    · exact dyadicMap_z P
  change GroupModel.centralShear cocycle _ (dyadicMap P (Dyadic.Filtration.gen j)) = _
  rw [hcan]
  apply GroupModel.ext
  · exact hbase.symm
  · change 0 + dyadicAdjustment P a.central b.central c.central _ = _
    rw [zero_add,dyadicAdjustment_apply]
    fin_cases j <;> rfl

theorem dyadicMapOfLifts_x (P : Fin 2) (a b c : Q) (ha : a.base = dyadicXVector P) :
    dyadicMapOfLifts P a b c Dyadic.D.x = a :=
  dyadicMapOfLifts_gen P a b c 0 ha
theorem dyadicMapOfLifts_y (P : Fin 2) (a b c : Q) (hb : b.base = dyadicYVector P) :
    dyadicMapOfLifts P a b c Dyadic.D.y = b :=
  dyadicMapOfLifts_gen P a b c 1 hb
theorem dyadicMapOfLifts_z (P : Fin 2) (a b c : Q) (hc : c.base = dyadicZVector P) :
    dyadicMapOfLifts P a b c Dyadic.D.z = c :=
  dyadicMapOfLifts_gen P a b c 2 hc

theorem dyadicMapOfLifts_comap_dimensionSubgroup (P : Fin 2) (a b c : Q) (n : ℕ) :
    (dimensionSubgroup F Q n).comap (dyadicMapOfLifts P a b c) =
      Dyadic.AlgebraD.dimensionSubgroup n := by
  let e := GroupModel.centralShear cocycle (dyadicAdjustment P a.central b.central c.central)
  have he : (dimensionSubgroup F Q n).comap e.toMonoidHom = dimensionSubgroup F Q n := by
    ext g
    change e g ∈ dimensionSubgroup F Q n ↔ g ∈ dimensionSubgroup F Q n
    constructor
    · intro h
      have hh := map_dimensionSubgroup_le F Q e.symm.toMonoidHom n ⟨e g,h,rfl⟩
      simpa using hh
    · intro h
      exact map_dimensionSubgroup_le F Q e.toMonoidHom n ⟨g,h,rfl⟩
  change (dimensionSubgroup F Q n).comap (e.toMonoidHom.comp (dyadicMap P)) = _
  rw [← Subgroup.comap_comap,he]
  exact dyadicMap_comap_dimensionSubgroup P n

/-- All layers inject for the adapted map. -/
theorem dyadicMapOfLifts_layers (P : Fin 2) (a b c : Q) (n : ℕ) :
    Function.Injective (layerMap F Dyadic.D (dyadicMapOfLifts P a b c) n) := by
  apply layer_injections_of_comap_dimensionSubgroup_eq F Dyadic.D Q
  intro m
  rw [dyadicMapOfLifts_comap_dimensionSubgroup,dyadic_dimensionSubgroup]

theorem dyadicCharacter_ofLifts (P : Fin 2) (a b c : Q) (j k : Fin 3) :
    (dyadicCharacter P k (dyadicMapOfLifts P a b c (Dyadic.Filtration.gen j))).toAdd =
      (Pi.single j (1 : F) : Fin 3 → F) k := by
  have hb : (dyadicMapOfLifts P a b c (Dyadic.Filtration.gen j)).base =
      (dyadicMap P (Dyadic.Filtration.gen j)).base := rfl
  change maskFunctional 8 _ (dyadicMapOfLifts P a b c (Dyadic.Filtration.gen j)).base = _
  rw [hb]
  exact dyadicCharacter_certificate P j k

end UnitDistance.Sqrt241.Retained
