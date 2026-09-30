module

public import UnitDistance.GroupAugmentationLayers
public import UnitDistance.GroupAugmentationNilpotence

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual layer injections and strict subgroup embeddings

Injectivity on all actual successive group layers is equivalent to pullback
equality of the actual dimension subgroups. For a finite p-group, proved
termination also forces injectivity of the group homomorphism itself.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
variable (R D P : Type*) [CommRing R] [Group D] [Group P] (f : D →* P)

/-- Layer injectivity recovers strictness by induction through the actual
dimension filtration, without a separate filtration compatibility premise. -/
theorem comap_dimensionSubgroup_eq_of_layer_injections
    (hinj : ∀ n, Function.Injective (layerMap R D f n)) (n : ℕ) :
    (dimensionSubgroup R P n).comap f = dimensionSubgroup R D n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply le_antisymm
    · intro g hg
      have hgn : g ∈ dimensionSubgroup R D n := by
        rw [← ih]
        exact dimensionSubgroup_antitone R P (Nat.le_succ n) hg
      exact (layerMap_injective_iff R D f n).mp (hinj n) g hgn hg
    · intro g hg
      exact map_dimensionSubgroup_le R D f (n+1) ⟨g,hg,rfl⟩

/-- A strict actual subgroup map is injective on every actual group layer. -/
theorem layer_injections_of_comap_dimensionSubgroup_eq
    (hstrict : ∀ n, (dimensionSubgroup R P n).comap f = dimensionSubgroup R D n) :
    ∀ n, Function.Injective (layerMap R D f n) := by
  intro n
  apply (layerMap_injective_iff R D f n).mpr
  intro g _ hg
  rw [← hstrict (n+1)]
  exact hg

/-- These are equivalent concrete group-filtration statements. -/
theorem layer_injections_iff_strict :
    (∀ n, Function.Injective (layerMap R D f n)) ↔
      ∀ n, (dimensionSubgroup R P n).comap f = dimensionSubgroup R D n :=
  ⟨comap_dimensionSubgroup_eq_of_layer_injections R D P f,
    layer_injections_of_comap_dimensionSubgroup_eq R D P f⟩

omit [CommRing R] in
/-- For an actual finite p-group, all-layer injectivity already implies
that the actual underlying group homomorphism is an embedding. -/
theorem injective_of_layer_injections [Finite D] (p : ℕ) [Fact p.Prime]
    (hD : IsPGroup p D)
    (hinj : ∀ n, Function.Injective (layerMap (ZMod p) D f n)) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro g hg
  have hmem : g ∈ (dimensionSubgroup (ZMod p) P (Nat.card D)).comap f := by
    change f g ∈ dimensionSubgroup (ZMod p) P (Nat.card D)
    rw [show f g = 1 from hg]
    exact Subgroup.one_mem _
  rw [comap_dimensionSubgroup_eq_of_layer_injections (ZMod p) D P f hinj,
    dimensionSubgroup_eq_bot_of_card_le D p hD _ (le_refl _)] at hmem
  exact hmem

end UnitDistance.GroupAugmentation
