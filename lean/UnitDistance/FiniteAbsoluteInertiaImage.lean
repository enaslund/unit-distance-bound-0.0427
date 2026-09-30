module

public import UnitDistance.LocalAbsoluteInertiaRestriction

@[expose] public section
set_option backward.privateInPublic true


/-! The actual image of absolute local inertia in a finite Galois local extension. -/
noncomputable section
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Actual Galois restriction through a supplied finite embedding. -/
def finiteAbsoluteRestriction (f : L →ₐ[K] SeparableClosure K) :
    Gal(SeparableClosure K/K) →* Gal(L/K) := by
  letI : Algebra L (SeparableClosure K) := f.toRingHom.toAlgebra
  letI : IsScalarTower K L (SeparableClosure K) := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    exact (f.commutes x).symm)
  exact AlgEquiv.restrictNormalHom (F := K) (K₁ := SeparableClosure K) L

theorem finiteAbsoluteRestriction_surjective (f : L →ₐ[K] SeparableClosure K) :
    Function.Surjective (finiteAbsoluteRestriction K L f) := by
  letI : Algebra L (SeparableClosure K) := f.toRingHom.toAlgebra
  letI : IsScalarTower K L (SeparableClosure K) := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    exact (f.commutes x).symm)
  exact AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := SeparableClosure K)

/-- Restriction is literal compatibility on the embedded finite field. -/
theorem finiteAbsoluteRestriction_commutes (f : L →ₐ[K] SeparableClosure K)
    (σ : Gal(SeparableClosure K/K)) (x : L) :
    σ (f x) = f (finiteAbsoluteRestriction K L f σ x) := by
  letI : Algebra L (SeparableClosure K) := f.toRingHom.toAlgebra
  letI : IsScalarTower K L (SeparableClosure K) := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro y
    exact (f.commutes y).symm)
  exact (AlgEquiv.restrictNormal_commutes σ L x).symm

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The image of the actual local absolute inertia kernel. -/
def finiteAbsoluteInertiaImage (f : L →ₐ[K] SeparableClosure K) : Subgroup Gal(L/K) :=
  (localResidueDegree K).toMonoidHom.ker.map (finiteAbsoluteRestriction K L f)

instance finiteAbsoluteInertiaImage_normal (f : L →ₐ[K] SeparableClosure K) :
    (finiteAbsoluteInertiaImage K L f).Normal :=
  Subgroup.Normal.map inferInstance (finiteAbsoluteRestriction K L f)
    (finiteAbsoluteRestriction_surjective K L f)

/-- Every member of the finite image has a literal compatible absolute inertia lift. -/
theorem exists_absoluteInertia_lift_of_mem_image (f : L →ₐ[K] SeparableClosure K)
    (τ : Gal(L/K)) (hτ : τ ∈ finiteAbsoluteInertiaImage K L f) :
    ∃ σ : Gal(SeparableClosure K/K), σ ∈ (localResidueDegree K).toMonoidHom.ker ∧
      ∀ x : L, σ (f x) = f (τ x) := by
  obtain ⟨σ,hσ,hστ⟩ := hτ
  refine ⟨σ,hσ,fun x => ?_⟩
  rw [finiteAbsoluteRestriction_commutes,hστ]

/-- The actual absolute inertia image is contained in actual finite residue inertia. -/
theorem finiteAbsoluteInertiaImage_le_residueInertia
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (f : L →ₐ[K] SeparableClosure K) :
    finiteAbsoluteInertiaImage K L f ≤
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
  intro τ hτ
  obtain ⟨σ,hσ,hσcompat⟩ := exists_absoluteInertia_lift_of_mem_image K L f τ hτ
  exact finiteResidueInertia_of_absoluteInertia K L f σ hσ τ hσcompat

end UnitDistance.ArithmeticProP
