module

public import UnitDistance.ArithmeticRetainedModel
public import UnitDistance.GroupAugmentationStrictness

@[expose] public section
set_option backward.privateInPublic true


/-! Actual augmentation layers of the actual retained Galois group and an
actual embedded copy of the specified finite dyadic group. This proves group
and filtration statements; it does not yet identify the image with a local
arithmetic decomposition group. -/
noncomputable section
namespace UnitDistance.ArithmeticRetained
open GroupAugmentation ArithmeticChosenGenus
abbrev F₂ := ZMod 2

/-- Actual dimension-subgroup membership transports through the proved group isomorphism. -/
theorem retained_dimension_iff (n : ℕ) (σ : Gal(RetainedField/ℚ)) :
    σ ∈ dimensionSubgroup F₂ (Gal(RetainedField/ℚ)) n ↔
      retainedModelEquiv.symm σ ∈ dimensionSubgroup F₂ RetainedQuadratic.Q n := by
  constructor
  · intro h
    exact map_dimensionSubgroup_le F₂ (Gal(RetainedField/ℚ)) retainedModelEquiv.symm.toMonoidHom n
      ⟨σ,h,rfl⟩
  · intro h
    have hh := map_dimensionSubgroup_le F₂ RetainedQuadratic.Q retainedModelEquiv.toMonoidHom n
      ⟨retainedModelEquiv.symm σ,h,rfl⟩
    simpa using hh

/-- The actual retained Galois group's third augmentation dimension subgroup is trivial. -/
theorem retained_dimensionSubgroup_three :
    dimensionSubgroup F₂ (Gal(RetainedField/ℚ)) 3=⊥ := by
  apply le_antisymm
  · intro σ hσ
    have h := (retained_dimension_iff 3 σ).mp hσ
    rw [ClassTwo.GroupModel.dimensionSubgroup_three,Subgroup.mem_bot] at h
    have hh := congrArg retainedModelEquiv h
    simpa using hh
  · exact bot_le

/-- An actual copy of the independently specified dyadic group in the actual Galois group. -/
def dyadicGaloisHom : Dyadic.D →* Gal(RetainedField/ℚ) :=
  retainedModelEquiv.toMonoidHom.comp RetainedQuadratic.dyadicMap

theorem dyadicGaloisHom_injective : Function.Injective dyadicGaloisHom :=
  retainedModelEquiv.injective.comp RetainedQuadratic.dyadicMap_injective

/-- All actual augmentation layers are compatible for this actual finite-group embedding. -/
theorem dyadicGaloisHom_comap_dimensionSubgroup (n : ℕ) :
    (dimensionSubgroup F₂ (Gal(RetainedField/ℚ)) n).comap dyadicGaloisHom=
      Dyadic.AlgebraD.dimensionSubgroup n := by
  ext g
  change dyadicGaloisHom g ∈ dimensionSubgroup F₂ (Gal(RetainedField/ℚ)) n ↔ _
  rw [retained_dimension_iff]
  change retainedModelEquiv.symm (retainedModelEquiv (RetainedQuadratic.dyadicMap g)) ∈ _ ↔ _
  rw [MulEquiv.symm_apply_apply]
  exact Iff.of_eq (congrArg (fun H : Subgroup Dyadic.D => g∈H)
    (RetainedQuadratic.dyadicMap_comap_dimensionSubgroup n))

theorem dyadicGaloisHom_layer_injective (n : ℕ) :
    Function.Injective (layerMap F₂ Dyadic.D dyadicGaloisHom n) :=
  layer_injections_of_comap_dimensionSubgroup_eq F₂ Dyadic.D (Gal(RetainedField/ℚ))
    dyadicGaloisHom (fun n => by
      simpa only [dyadic_dimensionSubgroup] using dyadicGaloisHom_comap_dimensionSubgroup n) n

end UnitDistance.ArithmeticRetained
