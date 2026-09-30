module

public import UnitDistance.PrimeIdealValuationInertia
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois

@[expose] public section
set_option backward.privateInPublic true


/-! Exact inertia comparison for the actual chosen finite local completion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open NumberField IsDedekindDomain
open scoped Pointwise ValuativeRel NNReal
namespace UnitDistance.PrimeCompletion
open HilbertRamification AlgebraicNumberTheory.Valuations
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
variable (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev chosenLocalField := ChosenFinitePlaceLocalizedCompletion (K:=ℚ) (L:=M) v
abbrev chosenLocalBase := ChosenFinitePlaceBaseCompletion (K:=ℚ) v
abbrev chosenLocalPrime := finitePlaceExtensionCentre v (chosenFinitePlaceExtension (L:=M) v)

def chosenLocalRestriction : Gal(chosenLocalField M v / chosenLocalBase v) →* Gal(M/ℚ) :=
  (absoluteValueDecompositionGroup ℚ (chosenFinitePlaceExtension (L:=M) v).1).subtype.comp
    (decompositionGroupEquivAlgebraicLocalizationAut (HeightOneSpectrum.adicAbv ℚ v)
      (RayClass.adicAbv_isNontrivial v) (chosenFinitePlaceExtension (L:=M) v)).symm.toMonoidHom

theorem chosenLocalRestriction_injective : Function.Injective (chosenLocalRestriction M v) :=
  Subtype.val_injective.comp (decompositionGroupEquivAlgebraicLocalizationAut
    (HeightOneSpectrum.adicAbv ℚ v) (RayClass.adicAbv_isNontrivial v)
    (chosenFinitePlaceExtension (L:=M) v)).symm.injective

/-- Intrinsic finite inertia is the norm displacement condition. -/
theorem chosenLocal_intrinsic_inertia_iff (τ : Gal(chosenLocalField M v / chosenLocalBase v)) :
    τ∈(galoisGroupResidueAlgEquivHomOfIsIntegralClosure (chosenLocalBase v)
      (chosenLocalField M v)).ker ↔
    ∀x : chosenLocalField M v, ‖x‖≤1 → ‖τ x-x‖<1 := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal]
  have hnorm (x : chosenLocalField M v) :
      (ValuativeRel.valuation (chosenLocalField M v)) x < 1 ↔ ‖x‖<1 := by
    have he := (ValuativeRel.isEquiv
      (ValuativeRel.valuation (chosenLocalField M v))
      (Valued.v : Valuation (chosenLocalField M v) ℝ≥0)).lt_iff_lt (x:=x) (y:=1)
    simp only [map_one] at he
    exact he.trans NNReal.coe_lt_coe
  have hmem (x : chosenLocalField M v) : x∈𝒪[chosenLocalField M v] ↔ ‖x‖≤1 :=
    localizedCompletion_mem_integers_iff_norm_le_one (HeightOneSpectrum.adicAbv ℚ v)
      (chosenFinitePlaceExtension (L:=M) v) (HeightOneSpectrum.isNonarchimedean_adicAbv ℚ v) x
  constructor
  · intro h x hx
    let y : 𝒪[chosenLocalField M v] := ⟨x,(hmem x).mpr hx⟩
    have hy := h y
    change ¬IsUnit (galoisGroupIntegerRingEquivOfIsIntegralClosure
      (chosenLocalBase v) (chosenLocalField M v) τ y-y) at hy
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hy
    exact (hnorm _).mp hy
  · intro h x
    change ¬IsUnit (galoisGroupIntegerRingEquivOfIsIntegralClosure
      (chosenLocalBase v) (chosenLocalField M v) τ x-x)
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact (hnorm _).mpr (h x ((hmem x).mp x.property))

/-- Actual ideal inertia and actual local intrinsic inertia correspond exactly. -/
theorem chosenLocalRestriction_mem_inertia_iff
    (τ : Gal(chosenLocalField M v / chosenLocalBase v)) :
    chosenLocalRestriction M v τ ∈ (chosenLocalPrime M v).asIdeal.inertia Gal(M/ℚ) ↔
      τ∈(galoisGroupResidueAlgEquivHomOfIsIntegralClosure (chosenLocalBase v)
        (chosenLocalField M v)).ker := by
  let w := chosenFinitePlaceExtension (L:=M) v
  let av := HeightOneSpectrum.adicAbv ℚ v
  let hv := RayClass.adicAbv_isNontrivial v
  let hw := finitePlaceExtension_nonarchimedean v w
  let σ := (decompositionGroupEquivAlgebraicLocalizationAut av hv w).symm τ
  let σv := localizationRamificationGroups_absoluteValueDecompositionGroupEquiv av hv w hw σ
  have h1 := prime_inertia_iff_valuation_inertia M v w σ
  have h2 := localizationRamificationGroups_valuationDecompositionGroupEquiv_mem_inertia_iff
    av hv w hw σv
  have heq : localizationRamificationGroups_valuationDecompositionGroupEquiv av hv w hw σv =
    localizationRamificationGroups_localDecompositionGroupEquiv av hv w hw τ := by
    simp only [σv,localizationRamificationGroups_valuationDecompositionGroupEquiv,
      MulEquiv.trans_apply,MulEquiv.symm_apply_apply,σ,MulEquiv.apply_symm_apply]
  rw [heq] at h2
  refine h1.trans (h2.symm.trans ?_)
  refine (ValuationSubring.mem_inertiaGroup_iff_sub_mem_nonunits
    (algebraicLocalizationValuationSubring av w hw)
    (localizationRamificationGroups_localDecompositionGroupEquiv av hv w hw τ)).trans ?_
  constructor
  · intro h
    apply (chosenLocal_intrinsic_inertia_iff M v τ).mpr
    intro x hx
    let xA : algebraicLocalizationValuationSubring av w hw := ⟨x,hx⟩
    exact (algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one _ _ _).mp (h xA)
  · intro h x
    apply (algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one _ _ _).mpr
    exact (chosenLocal_intrinsic_inertia_iff M v τ).mp h x x.property

end UnitDistance.PrimeCompletion
