module

public import UnitDistance.LocalArtinRestriction
public import UnitDistance.FiniteInertiaFixedField
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization

@[expose] public section
set_option backward.privateInPublic true


/-! Actual local Artin images of integer units vanish on unramified fixed fields. -/
noncomputable section
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The local Artin image of every actual valuation-ring unit lies in the
abelianized image of a normal subgroup with unramified fixed field. -/
theorem localArtin_integerUnit_mem_of_fixedField_unramified
    (J : Subgroup Gal(L/K)) [J.Normal] :
    let E := IntermediateField.fixedField J
    letI : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
    letI : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
    letI : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
    letI : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
      finiteExtensionSpectralValuation_hasExtension K E
    letI : Module.Finite 𝒪[K] 𝒪[E] := localCompleteDVF_integerRing_moduleFinite K E
    IsUnramifiedValuedExtension K E → ∀ u : 𝒪[K]ˣ,
      localArtinMonoidHom K L (integerUnitsToFieldUnits K u) ∈ J.map Abelianization.of := by
  let E := IntermediateField.fixedField J
  letI : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  letI : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  letI : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  letI : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  letI : Module.Finite 𝒪[K] 𝒪[E] := localCompleteDVF_integerRing_moduleFinite K E
  letI : IsIntegralClosure 𝒪[E] 𝒪[K] E := localCompleteDVF_integerRing_isIntegralClosure K E
  change IsUnramifiedValuedExtension K E → _
  intro hE u
  letI := hE
  letI : IsCyclic Gal(E/K) := isCyclic_galoisGroup_of_unramifiedValuation K E
  letI : CommGroup Gal(E/K) := IsCyclic.commGroup
  have hu : localArtinMonoidHom K E (integerUnitsToFieldUnits K u) = 1 := by
    rw [localArtinMonoidHom_eq_frobenius_zpow, valuationMap_apply,
      v_integerUnitsToFieldUnits, zpow_zero]
  obtain ⟨σ,hσ⟩ := QuotientGroup.mk_surjective
    (localArtinMonoidHom K L (integerUnitsToFieldUnits K u))
  change Abelianization.of σ = _ at hσ
  refine ⟨σ,?_,hσ⟩
  have hm := localArtinMonoidHom_abelianized_restrict_tower K E L
    (integerUnitsToFieldUnits K u)
  rw [← hσ, Abelianization.map_of, hu] at hm
  have ht : σ.restrictNormal E = 1 := by
    apply (Abelianization.equivOfComm (H := Gal(E/K))).injective
    change Abelianization.of ((AlgEquiv.restrictNormalHom E) σ) = 1
    exact hm
  rw [← IntermediateField.fixingSubgroup_fixedField J, ← E.restrictNormalHom_ker]
  exact ht

end UnitDistance.ArithmeticProP
