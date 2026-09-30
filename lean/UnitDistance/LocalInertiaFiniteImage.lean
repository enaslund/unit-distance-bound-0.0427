module

public import UnitDistance.FiniteAbsoluteInertiaImage
public import UnitDistance.FiniteInertiaFixedField
public import UnitDistance.LocalArtinUnitContainment
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.LocalFiniteInertiaUnramified

@[expose] public section
set_option backward.privateInPublic true


/-! Actual absolute inertia surjects onto finite inertia. The fixed field of
its actual finite image is unramified; finite Galois correspondence gives the
reverse inclusion. Actual local Artin unit images consequently lie in the
abelianized finite inertia image. -/
noncomputable section
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory
open ClassFieldTower.Martinet.Shafarevich

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The fixed field of the actual finite image of absolute inertia is unramified. -/
theorem finiteAbsoluteInertiaImage_fixedField_isUnramified
    (f : L →ₐ[K] SeparableClosure K) :
    let E := IntermediateField.fixedField (finiteAbsoluteInertiaImage K L f)
    letI : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
    letI : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
    letI : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
    letI : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
      finiteExtensionSpectralValuation_hasExtension K E
    letI : Module.Finite 𝒪[K] 𝒪[E] := localCompleteDVF_integerRing_moduleFinite K E
    IsUnramifiedValuedExtension K E := by
  let E := IntermediateField.fixedField (finiteAbsoluteInertiaImage K L f)
  letI : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  letI : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  letI : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  letI : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  letI : Module.Finite 𝒪[K] 𝒪[E] := localCompleteDVF_integerRing_moduleFinite K E
  letI : IsIntegralClosure 𝒪[E] 𝒪[K] E := localCompleteDVF_integerRing_isIntegralClosure K E
  let fE : E →ₐ[K] SeparableClosure K := f.comp E.val
  have hfix : ∀ σ ∈ (localResidueDegree K).toMonoidHom.ker,
      ∀ x : E, σ (fE x) = fE x := by
    intro σ hσ x
    have hm : finiteAbsoluteRestriction K L f σ ∈ finiteAbsoluteInertiaImage K L f :=
      ⟨σ,hσ,rfl⟩
    have hx := (IntermediateField.mem_fixedField_iff _ _).mp x.property
      (finiteAbsoluteRestriction K L f σ) hm
    calc
      σ (fE x) = f (finiteAbsoluteRestriction K L f σ (x : L)) :=
        finiteAbsoluteRestriction_commutes K L f σ (x : L)
      _ = f (x : L) := congrArg f hx
      _ = fE x := rfl
  exact localFiniteExtension_isUnramified_of_inertiaFixes K E fE hfix

variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- Actual absolute inertia has exactly the finite residue inertia as its image. -/
theorem finiteAbsoluteInertiaImage_eq_residueInertia
    (f : L →ₐ[K] SeparableClosure K) :
    finiteAbsoluteInertiaImage K L f =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
  apply le_antisymm (finiteAbsoluteInertiaImage_le_residueInertia K L f)
  exact finiteResidueInertia_le_of_fixedField_unramified K L
    (finiteAbsoluteInertiaImage K L f)
    (finiteAbsoluteInertiaImage_fixedField_isUnramified K L f)

/-- Every actual finite inertia automorphism has a compatible actual absolute inertia lift. -/
theorem exists_absoluteInertia_lift
    (f : L →ₐ[K] SeparableClosure K) (τ : Gal(L/K))
    (hτ : τ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker) :
    ∃ σ : Gal(SeparableClosure K/K), σ ∈ (localResidueDegree K).toMonoidHom.ker ∧
      ∀ x : L, σ (f x) = f (τ x) := by
  apply exists_absoluteInertia_lift_of_mem_image K L f τ
  rw [finiteAbsoluteInertiaImage_eq_residueInertia]
  exact hτ

/-- Actual integer units have Artin image in the actual finite inertia image. -/
theorem localArtin_integerUnit_mem_residueInertia_image (u : 𝒪[K]ˣ) :
    localArtinMonoidHom K L (integerUnitsToFieldUnits K u) ∈
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker.map Abelianization.of := by
  let f := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  have h := localArtin_integerUnit_mem_of_fixedField_unramified K L
    (finiteAbsoluteInertiaImage K L f)
    (finiteAbsoluteInertiaImage_fixedField_isUnramified K L f) u
  rw [finiteAbsoluteInertiaImage_eq_residueInertia] at h
  exact h

end UnitDistance.ArithmeticProP
