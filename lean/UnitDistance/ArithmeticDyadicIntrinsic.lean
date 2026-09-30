module

public import UnitDistance.ArithmeticDyadicValuation
public import UnitDistance.ArithmeticDyadicAbelianization
public import UnitDistance.PadicFiniteGaloisIntrinsic
public import UnitDistance.IntrinsicInertiaComparison
public import UnitDistance.LocalResidueSurjectivity
public import UnitDistance.LocalArtinUnitIndex
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.PrincipalUnits

@[expose] public section
set_option backward.privateInPublic true


/-! Actual intrinsic local-field structures and reciprocity for the retained dyadic field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ValuativeRel
namespace UnitDistance.ArithmeticDyadic
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev intrinsicNormedField : NontriviallyNormedField LocalField :=
  finiteExtensionSpectralNormedField ℚ_[2] LocalField
local instance : NontriviallyNormedField LocalField := intrinsicNormedField
abbrev intrinsicValuativeRel : ValuativeRel LocalField :=
  finiteExtensionSpectralValuativeRel ℚ_[2] LocalField
local instance : ValuativeRel LocalField := intrinsicValuativeRel
abbrev intrinsicLocalField : IsNonarchimedeanLocalField LocalField :=
  finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[2] LocalField
local instance : IsNonarchimedeanLocalField LocalField := intrinsicLocalField
abbrev intrinsicHasExtension :
    Valuation.HasExtension (ValuativeRel.valuation ℚ_[2]) (ValuativeRel.valuation LocalField) :=
  finiteExtensionSpectralValuation_hasExtension ℚ_[2] LocalField
local instance : Valuation.HasExtension (ValuativeRel.valuation ℚ_[2]) (ValuativeRel.valuation LocalField) :=
  intrinsicHasExtension
abbrev intrinsicIntegralClosure : IsIntegralClosure 𝒪[LocalField] 𝒪[ℚ_[2]] LocalField :=
  localCompleteDVF_integerRing_isIntegralClosure ℚ_[2] LocalField
local instance : IsIntegralClosure 𝒪[LocalField] 𝒪[ℚ_[2]] LocalField := intrinsicIntegralClosure
local instance : localValuation.valuation.Compatible :=
  PadicFiniteGalois.target_intrinsicCompatible 2 LocalField

abbrev intrinsicResidueAction := galoisGroupResidueAlgEquivHomOfIsIntegralClosure ℚ_[2] LocalField
abbrev intrinsicInertia := intrinsicResidueAction.ker
abbrev intrinsicResidueDegree := Module.finrank 𝓀[ℚ_[2]] 𝓀[LocalField]

theorem intrinsicInertia_eq : intrinsicInertia=inertia := by
  ext σ
  exact ArithmeticProP.intrinsicInertia_iff_lowerRamification_zero ℚ_[2] LocalField
    localBaseValuation.toDVF localValuation.toDVF localUnique σ

theorem intrinsicInertia_square (σ : intrinsicInertia) : (σ : G)^2=1 := by
  apply actual_inertia_square ⟨σ,?_⟩
  simpa only [←intrinsicInertia_eq] using σ.property

def intrinsicUnitEquiv : ℤ_[2]ˣ ≃* 𝒪[ℚ_[2]]ˣ :=
  Units.mapEquiv (LocalFieldTheory.Padic.integerRingEquivPadicInt 2).symm.toMulEquiv

def intrinsicUnitArtin : ℤ_[2]ˣ →* Abelianization G :=
  ((localArtinMonoidHom ℚ_[2] LocalField).comp (integerUnitsToFieldUnits ℚ_[2])).comp
    intrinsicUnitEquiv.toMonoidHom

theorem intrinsicUnitArtin_range_index : intrinsicUnitArtin.range.index=intrinsicResidueDegree := by
  have hr : intrinsicUnitArtin.range=
      ((localArtinMonoidHom ℚ_[2] LocalField).comp (integerUnitsToFieldUnits ℚ_[2])).range := by
    rw [intrinsicUnitArtin,MonoidHom.range_comp,
      intrinsicUnitEquiv.toMonoidHom.range_eq_top_of_surjective intrinsicUnitEquiv.surjective,
      MonoidHom.range_eq_map]
  rw [hr]
  exact ArithmeticProP.localArtin_integerUnits_range_index ℚ_[2] LocalField

theorem inertia_card_of_unit_image_exponent_two (hu : ∀ a,intrinsicUnitArtin a^2=1) :
    intrinsicResidueDegree=4 ∧ Nat.card inertia=8 := by
  have hcard : Nat.card (𝓀[LocalField] ≃ₐ[𝓀[ℚ_[2]]] 𝓀[LocalField])=intrinsicResidueDegree :=
    residueAlgEquiv_card_eq_finrank ℚ_[2] LocalField
  have h := residue_inertia_cards intrinsicResidueAction
    (ArithmeticProP.intrinsicResidueAction_surjective ℚ_[2] LocalField)
    intrinsicUnitArtin hu (intrinsicUnitArtin_range_index.trans hcard.symm)
  rw [hcard] at h
  change intrinsicResidueDegree=4 ∧ Nat.card intrinsicInertia=8 at h
  rwa [intrinsicInertia_eq] at h

end UnitDistance.ArithmeticDyadic
