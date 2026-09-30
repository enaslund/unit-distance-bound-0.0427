module

public import UnitDistance.IntegralClosureValuationTower
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! The actual finite inertia group is contained in every normal subgroup
whose fixed field is unramified. -/
noncomputable section
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- An unramified actual fixed field forces containment of actual residue inertia. -/
theorem finiteResidueInertia_le_of_fixedField_unramified
    (J : Subgroup Gal(L/K)) [J.Normal] :
    let E := IntermediateField.fixedField J
    letI : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
    letI : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
    letI : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
    letI : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
      finiteExtensionSpectralValuation_hasExtension K E
    letI : Module.Finite 𝒪[K] 𝒪[E] := localCompleteDVF_integerRing_moduleFinite K E
    IsUnramifiedValuedExtension K E →
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ≤ J := by
  let E := IntermediateField.fixedField J
  letI : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  letI : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  letI : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  letI : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  letI : Module.Finite 𝒪[K] 𝒪[E] := localCompleteDVF_integerRing_moduleFinite K E
  letI : IsIntegralClosure 𝒪[E] 𝒪[K] E := localCompleteDVF_integerRing_isIntegralClosure K E
  letI : Valuation.HasExtension (ValuativeRel.valuation E) (ValuativeRel.valuation L) :=
    valuation_hasExtension_of_integralClosure_tower K E L
  change IsUnramifiedValuedExtension K E → _
  intro hE
  letI := hE
  intro τ hτ
  have ht : τ.restrictNormal E = 1 :=
    finiteResidueInertia_restrictNormal_eq_one_of_unramified K E L τ hτ
  rw [← IntermediateField.fixingSubgroup_fixedField J, ← E.restrictNormalHom_ker]
  exact ht

end UnitDistance.ArithmeticProP
