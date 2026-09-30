module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import Mathlib.FieldTheory.Normal.Defs

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite inertia restricts through a valued field tower, and hence
fixes every unramified intermediate field pointwise. -/
noncomputable section
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

variable (K E L : Type) [Field K] [ValuativeRel K]
  [Field E] [ValuativeRel E] [Field L] [ValuativeRel L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
  [Normal K E]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [Valuation.HasExtension (ValuativeRel.valuation E) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[E] 𝒪[K] E] [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- Restriction of an actual residue-inertia element is again in residue inertia. -/
theorem finiteResidueInertia_restrictNormal_mem
    (σ : Gal(L/K))
    (hσ : σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker) :
    σ.restrictNormal E ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K E).ker := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_residue_eq] at hσ ⊢
  intro x
  apply (algebraMap 𝓀[E] 𝓀[L]).injective
  rw [residueField_algebraMap_residue, residueField_algebraMap_residue]
  have hmap : algebraMap 𝒪[E] 𝒪[L]
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K E (σ.restrictNormal E) x) =
      galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
        (algebraMap 𝒪[E] 𝒪[L] x) := by
    apply Subtype.ext
    change algebraMap E L (σ.restrictNormal E (x : E)) = σ (algebraMap E L (x : E))
    exact AlgEquiv.restrictNormal_commutes σ E (x : E)
  rw [hmap]
  exact hσ (algebraMap 𝒪[E] 𝒪[L] x)

/-- Inertia fixes every actual unramified intermediate local field. -/
theorem finiteResidueInertia_restrictNormal_eq_one_of_unramified
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [FiniteDimensional K E] [IsGalois K E] [Module.Finite 𝒪[K] 𝒪[E]]
    [IsUnramifiedValuedExtension K E]
    (σ : Gal(L/K))
    (hσ : σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker) :
    σ.restrictNormal E = 1 := by
  apply galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation K E
  rw [map_one]
  exact finiteResidueInertia_restrictNormal_mem K E L σ hσ

end UnitDistance.ArithmeticProP
