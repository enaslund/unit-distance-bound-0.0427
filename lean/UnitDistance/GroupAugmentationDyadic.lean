module

public import UnitDistance.GroupAugmentationLayers
public import UnitDistance.GroupAugmentationGenerators
public import UnitDistance.DyadicDimensionCertificate

@[expose] public section
set_option backward.privateInPublic true


/-!
# The concrete dyadic group inside arbitrary ambient groups

This attaches the previously kernel-certified dyadic augmentation filtration
to the general group-algebra construction. Two genuine quotient-layer
injections suffice for all-degree compatibility. Producing those injections
from the manuscript's actual global quotient remains a structural obligation.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
open Dyadic

@[simp] theorem dyadic_delta (g : D) : delta F g = AlgebraD.delta g := rfl

/-- Both augmentations are the ordinary sum of group-algebra coefficients. -/
theorem dyadic_augmentation (a : AlgebraD) :
    augmentation F D a = AlgebraD.augmentation a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single g r => simp

/-- The generic powers agree with the independently defined and previously
certified concrete dyadic powers, not just with their dimensions. -/
theorem dyadic_power (n : ℕ) : power F D n = AlgebraD.augmentationPower n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Submodule.span F {v | ∃ a ∈ power F D n,
      ∃ b : AlgebraD, augmentation F D b = 0 ∧ v = a*b} =
      Submodule.span F {v | ∃ a ∈ AlgebraD.augmentationPower n,
      ∃ b : AlgebraD, AlgebraD.augmentation b = 0 ∧ v = a*b}
    simp only [ih, dyadic_augmentation]

theorem dyadic_dimensionSubgroup (n : ℕ) :
    dimensionSubgroup F D n = AlgebraD.dimensionSubgroup n := by
  ext g
  change delta F g - 1 ∈ power F D n ↔
    AlgebraD.delta g - 1 ∈ AlgebraD.augmentationPower n
  rw [dyadic_delta, dyadic_power]

theorem dyadic_dimensionSubgroup_three : dimensionSubgroup F D 3 = ⊥ := by
  rw [dyadic_dimensionSubgroup, AlgebraD.dimensionSubgroup_three]

/-- The three displayed concrete elements generate the actual dyadic group. -/
theorem dyadic_generators : Subgroup.closure (Set.range Filtration.gen) = ⊤ := by
  have hset : Set.range Filtration.gen = ({D.x, D.y, D.z} : Set D) := by
    ext g
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp [Filtration.gen]
    · intro hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
  rw [hset]
  exact D.generators

/-- The actual dyadic augmentation sequence is strict at every degree. -/
theorem dyadic_foxMap_strict (n : ℕ) :
    (coefficientPower F D (ι := Fin 3) n).map (foxMap F D Filtration.gen) =
      AlgebraD.augmentationPower (n+1) := by
  rw [foxMap_strict F D Filtration.gen dyadic_generators, dyadic_power]

variable {P : Type*} [Group P]

/-- The manuscript's low-layer reduction for the actual order-32 group,
valid for any ambient group and therefore for any finite ambient 2-group. -/
theorem dyadic_comap_dimensionSubgroup
    (f : D →* P)
    (hfirst : Function.Injective (layerMap F D f 1))
    (hsecond : Function.Injective (layerMap F D f 2)) (n : ℕ) :
    (dimensionSubgroup F P n).comap f = AlgebraD.dimensionSubgroup n := by
  rw [← dyadic_dimensionSubgroup]
  exact comap_dimensionSubgroup_eq_of_first_two_layers F D f
    dyadic_dimensionSubgroup_three hfirst hsecond n

/-- The first two layer injections already force the underlying dyadic
homomorphism to be an embedding. No independent injectivity assumption is needed. -/
theorem dyadic_injective_of_layers (f : D →* P)
    (hfirst : Function.Injective (layerMap F D f 1))
    (hsecond : Function.Injective (layerMap F D f 2)) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro g hg
  have hmem : g ∈ (dimensionSubgroup F P 3).comap f := by
    change f g ∈ dimensionSubgroup F P 3
    rw [show f g = 1 from hg]
    exact Subgroup.one_mem _
  rwa [dyadic_comap_dimensionSubgroup f hfirst hsecond,
    AlgebraD.dimensionSubgroup_three] at hmem

/-- This is the actual intersection identity `f(D) ∩ Dₙ(P) = f(Dₙ(D))`
used before extending an adapted basis. It is not yet a PBW theorem. -/
theorem dyadic_range_inf_dimensionSubgroup (f : D →* P)
    (hfirst : Function.Injective (layerMap F D f 1))
    (hsecond : Function.Injective (layerMap F D f 2)) (n : ℕ) :
    f.range ⊓ dimensionSubgroup F P n = (AlgebraD.dimensionSubgroup n).map f := by
  ext p
  constructor
  · rintro ⟨⟨g,rfl⟩, hg⟩
    refine ⟨g, ?_, rfl⟩
    rw [← dyadic_comap_dimensionSubgroup f hfirst hsecond n]
    exact hg
  · rintro ⟨g,hg,rfl⟩
    refine ⟨⟨g,rfl⟩, ?_⟩
    rw [← dyadic_comap_dimensionSubgroup f hfirst hsecond n] at hg
    exact hg

end UnitDistance.GroupAugmentation
