module

public import UnitDistance.ArithmeticDyadicGenerators
public import UnitDistance.RetainedDyadicLifts
public import UnitDistance.ArithmeticRetainedAugmentation

@[expose] public section
set_option backward.privateInPublic true


/-! Actual degree 32 and the actual dyadic Galois group model after base
change of the retained number field to Q₂. The chosen three local generators
come from true genus signs; no local degree is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticDyadic
open ArithmeticRetained GroupAugmentation
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def dyadicModelMap : Dyadic.D →* RetainedQuadratic.Q :=
  RetainedQuadratic.dyadicMapOfLifts (model (generator 0)) (model (generator 1)) (model (generator 2))

theorem dyadicModelMap_injective : Function.Injective dyadicModelMap :=
  RetainedQuadratic.dyadicMapOfLifts_injective _ _ _

theorem dyadicModelMap_range : dyadicModelMap.range=model.range := by
  have h0 : (model (generator 0)).base=RetainedQuadratic.binaryVector 7 2 := generator_base 0
  have h1 : (model (generator 1)).base=RetainedQuadratic.binaryVector 7 53 := generator_base 1
  have h2 : (model (generator 2)).base=RetainedQuadratic.binaryVector 7 89 := generator_base 2
  rw [show dyadicModelMap=RetainedQuadratic.dyadicMapOfLifts
    (model (generator 0)) (model (generator 1)) (model (generator 2)) from rfl,
    RetainedQuadratic.dyadicMapOfLifts_range _ _ _ h0 h1 h2]
  have hs : model '' Set.range generator=
      ({model (generator 0),model (generator 1),model (generator 2)} : Set RetainedQuadratic.Q) := by
    ext q
    constructor
    · rintro ⟨σ,⟨i,rfl⟩,rfl⟩
      fin_cases i <;> simp
    · intro h
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
      rcases h with rfl | rfl | rfl
      · exact ⟨generator 0,⟨0,rfl⟩,rfl⟩
      · exact ⟨generator 1,⟨1,rfl⟩,rfl⟩
      · exact ⟨generator 2,⟨2,rfl⟩,rfl⟩
  rw [← hs,← MonoidHom.map_closure,generators]
  ext q
  simp only [Subgroup.mem_map,Subgroup.mem_top,true_and,MonoidHom.mem_range]

/-- An actual isomorphism D32 ≃ Gal(M·Q₂/Q₂). -/
def galoisEquiv : Dyadic.D ≃* G :=
  (MonoidHom.ofInjective dyadicModelMap_injective).trans
    ((MulEquiv.subgroupCongr dyadicModelMap_range).trans
      (MonoidHom.ofInjective model_injective).symm)

theorem model_galoisEquiv (d : Dyadic.D) : model (galoisEquiv d)=dyadicModelMap d := by
  have h := (MonoidHom.ofInjective model_injective).apply_symm_apply
    (MulEquiv.subgroupCongr dyadicModelMap_range ((MonoidHom.ofInjective dyadicModelMap_injective) d))
  exact congrArg Subtype.val h

theorem galoisEquiv_x : galoisEquiv Dyadic.D.x=generator 0 := by
  apply model_injective
  rw [model_galoisEquiv]
  exact RetainedQuadratic.dyadicMapOfLifts_x _ _ _ (generator_base 0)
theorem galoisEquiv_y : galoisEquiv Dyadic.D.y=generator 1 := by
  apply model_injective
  rw [model_galoisEquiv]
  exact RetainedQuadratic.dyadicMapOfLifts_y _ _ _ (generator_base 1)
theorem galoisEquiv_z : galoisEquiv Dyadic.D.z=generator 2 := by
  apply model_injective
  rw [model_galoisEquiv]
  exact RetainedQuadratic.dyadicMapOfLifts_z _ _ _ (generator_base 2)

/-- The true local Galois group has order32. -/
theorem galoisGroup_card : Nat.card G=32 := by
  rw [← Nat.card_congr galoisEquiv.toEquiv,Nat.card_eq_fintype_card,Dyadic.D.card]

/-- The actual field degree is32, derived from its true Galois group. -/
theorem localField_degree : Module.finrank ℚ_[2] LocalField=32 := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact galoisGroup_card

/-- Actual dyadic restriction into the actual retained Galois group. -/
def dyadicGaloisMap : Dyadic.D →* Gal(RetainedField/ℚ) := restriction.comp galoisEquiv.toMonoidHom

theorem dyadicGaloisMap_comap_dimensionSubgroup (n : ℕ) :
    (dimensionSubgroup (ZMod 2) Gal(RetainedField/ℚ) n).comap dyadicGaloisMap=
      Dyadic.AlgebraD.dimensionSubgroup n := by
  ext d
  change dyadicGaloisMap d∈dimensionSubgroup (ZMod 2) Gal(RetainedField/ℚ) n ↔ _
  rw [retained_dimension_iff]
  change model (galoisEquiv d)∈dimensionSubgroup (ZMod 2) RetainedQuadratic.Q n ↔ _
  rw [model_galoisEquiv]
  exact Iff.of_eq (congrArg (fun H : Subgroup Dyadic.D => d∈H)
    (RetainedQuadratic.dyadicMapOfLifts_comap_dimensionSubgroup
      (model (generator 0)) (model (generator 1)) (model (generator 2)) n))

/-- Every actual local augmentation layer injects into the retained global layer. -/
theorem dyadicGaloisMap_layer_injective (n : ℕ) :
    Function.Injective (layerMap (ZMod 2) Dyadic.D dyadicGaloisMap n) :=
  layer_injections_of_comap_dimensionSubgroup_eq (ZMod 2) Dyadic.D Gal(RetainedField/ℚ)
    dyadicGaloisMap (fun n => by
      simpa only [dyadic_dimensionSubgroup] using dyadicGaloisMap_comap_dimensionSubgroup n) n

end UnitDistance.ArithmeticDyadic
