module

public import UnitDistance.DyadicGraded

@[expose] public section
set_option backward.privateInPublic true


/-! The actual augmentation dimension subgroups of the concrete dyadic group. -/

noncomputable section
namespace UnitDistance.Dyadic.AlgebraD
open Filtration

/-- The ordinary dimension subgroup defined by the actual augmentation power. -/
def dimensionSubgroup (n : ℕ) : Subgroup D where
  carrier := {g | delta g - 1 ∈ augmentationPower n}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    have hm := stage_right_group n h (delta g - 1)
      ((stage_eq_augmentationPower n).symm ▸ hg)
    rw [stage_eq_augmentationPower] at hm
    have he : delta (g * h) - 1 = (delta g - 1) * delta h + (delta h - 1) := by
      rw [← delta_mul]
      noncomm_ring
    change delta (g * h) - 1 ∈ augmentationPower n
    rw [he]
    exact (augmentationPower n).add_mem hm hh
  inv_mem' {g} hg := by
    have hm := stage_right_group n g⁻¹ (delta g - 1)
      ((stage_eq_augmentationPower n).symm ▸ hg)
    rw [stage_eq_augmentationPower] at hm
    have he : delta g⁻¹ - 1 = -((delta g - 1) * delta g⁻¹) := by
      simp [sub_mul, delta_mul]
    change delta g⁻¹ - 1 ∈ augmentationPower n
    rw [he]
    exact (augmentationPower n).neg_mem hm

def groupDifferenceVector (i : Fin 32) : V := Pi.single i 1 - Pi.single 0 1

theorem coefficients_group_difference (i : Fin 32) :
    coefficients (delta (D.ofIndex i) - 1) = groupDifferenceVector i := by
  ext j
  have he : D.ofIndex i = D.ofIndex j ↔ i = j := D.indexEquiv.symm.injective.eq_iff
  have hz : (1 : D) = D.ofIndex j ↔ (0 : Fin 32) = j := by
    have h0 : D.indexEquiv.symm (0 : Fin 32) = 1 := by decide
    rw [← h0]
    exact D.indexEquiv.symm.injective.eq_iff
  simp [coefficients_apply, delta, MonoidAlgebra.one_def, Finsupp.single_apply,
    groupDifferenceVector, Pi.single_apply, he, hz, eq_comm]

theorem dimensionSubgroup_antitone : Antitone dimensionSubgroup := by
  intro m n h g hg
  exact augmentationPower_antitone h hg

theorem dimensionSubgroup_one : dimensionSubgroup 1 = ⊤ := by
  ext g
  change delta g - 1 ∈ augmentationPower 1 ↔ g ∈ (⊤ : Subgroup D)
  rw [augmentationPower_one]
  simp

end UnitDistance.Dyadic.AlgebraD
