module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.ClosedSubgroups
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionField
public import UnitDistance.AbsoluteProPRestriction

@[expose] public section
set_option backward.privateInPublic true


/-! Compact actual local decomposition and inertia parameter spaces, with
continuous restriction to the constructed maximal pro-p extension. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.Martinet.Shafarevich

variable (F : Type) [Field F] [NumberField F]

/-- The actual chosen absolute decomposition subgroup is compact. -/
theorem finitePlaceAbsoluteDecomposition_compactSpace
    (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (finitePlaceAbsoluteDecompositionGroup F v) :=
  isCompact_iff_compactSpace.mp
    (HilbertRamification.absoluteValueDecompositionGroup_isClosed
      F (finitePlaceAbsoluteValueExtension F v).1).isCompact

/-- Actual absolute inertia is closed inside the chosen decomposition group. -/
theorem finitePlaceAbsoluteInertia_isClosed
    (v : HeightOneSpectrum (𝓞 F)) :
    IsClosed (finitePlaceAbsoluteInertiaSubgroup F v :
      Set (finitePlaceAbsoluteDecompositionGroup F v)) := by
  let A := finitePlaceAbsoluteValuationSubring F v
  let I := RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut F A
  have hset : (finitePlaceAbsoluteInertiaSubgroup F v :
      Set (finitePlaceAbsoluteDecompositionGroup F v)) =
      (fun σ : finitePlaceAbsoluteDecompositionGroup F v => σ.1) ⁻¹' (I : Set _) := by
    ext σ
    constructor
    · intro hσ
      exact ⟨finitePlaceAbsoluteDecompositionValuationEquiv F v σ, hσ, rfl⟩
    · rintro ⟨τ, hτ, hτσ⟩
      have he : τ = finitePlaceAbsoluteDecompositionValuationEquiv F v σ :=
        Subtype.ext hτσ
      change finitePlaceAbsoluteDecompositionValuationEquiv F v σ ∈
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup F A
      exact he ▸ hτ
  rw [hset]
  exact (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut_isClosed
    F A).preimage continuous_subtype_val

/-- The actual chosen absolute inertia subgroup is compact. -/
theorem finitePlaceAbsoluteInertia_compactSpace
    (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (finitePlaceAbsoluteInertiaSubgroup F v) := by
  letI := finitePlaceAbsoluteDecomposition_compactSpace F v
  exact isCompact_iff_compactSpace.mp (finitePlaceAbsoluteInertia_isClosed F v).isCompact

/-- The actual local inertia/decomposition pair space is compact. -/
theorem finitePlaceAbsoluteInertiaDecomposition_compactSpace
    (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (finitePlaceAbsoluteInertiaSubgroup F v ×
      finitePlaceAbsoluteDecompositionGroup F v) := by
  letI := finitePlaceAbsoluteDecomposition_compactSpace F v
  letI := finitePlaceAbsoluteInertia_compactSpace F v
  infer_instance

/-- Actual absolute decomposition restricts continuously to the maximal group. -/
def finitePlaceDecompositionToMaximalProPOutside
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    finitePlaceAbsoluteDecompositionGroup ℚ v →ₜ*
      (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T) :=
  (absoluteToMaximalProPOutside p T).comp (finitePlaceAbsoluteDecompositionInclusion ℚ v)

/-- Actual absolute inertia restricts continuously to the maximal group. -/
def finitePlaceInertiaToMaximalProPOutside
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    finitePlaceAbsoluteInertiaSubgroup ℚ v →ₜ*
      (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T) :=
  (finitePlaceDecompositionToMaximalProPOutside p T v).comp
    (finitePlaceAbsoluteInertiaInclusion ℚ v)

@[simp] theorem finitePlaceInertiaToMaximalProPOutside_apply
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (σ : finitePlaceAbsoluteInertiaSubgroup ℚ v) :
    finitePlaceInertiaToMaximalProPOutside p T v σ =
      finitePlaceDecompositionToMaximalProPOutside p T v σ.1 := rfl

end UnitDistance.ArithmeticProP
