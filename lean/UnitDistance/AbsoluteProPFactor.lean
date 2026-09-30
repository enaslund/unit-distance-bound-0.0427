/-
Adapted from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Source: SawinTotallyRealTowers/AbsoluteRealProPFactor.lean.
Modified: the kernel field need only satisfy actual finite ramification support; total reality is removed.
-/
module

public import UnitDistance.AbsoluteProPRestriction
public import UnitDistance.FinitePExtension
public import UnitDistance.MaximalProPOutside
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.RamificationSupport
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteDiscreteKernelField
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceInertiaFixedUnramified
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Topologies.QuotientMaps
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Factoring representations through the maximal pro-p compositum

A discrete p-group representation killing finite inertia outside the chosen
support has an actual finite Galois
kernel field satisfying the defining local conditions. Its inclusion in the
constructed compositum gives a continuous factorization through restriction.
The target need not be finite, and the argument does not require p to be odd.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.ArithmeticProP

open ClassFieldTower.Sawin ClassFieldTower.Martinet.Shafarevich

-- Keep the algebraic-closure and intermediate-field scalar structures
-- generic until the two local comparisons have been proved.
section KernelLocalization

private local instance kernelLocalizationGalois
    (F : Type) [Field F] [NumberField F]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (s : Field.absoluteGaloisGroup F →ₜ* Q) :
    IsGalois F (absoluteDiscreteKernelField F s) :=
  absoluteDiscreteKernelField_isGalois F s

private theorem discreteKernel_chosenUnramified
    (F : Type) [Field F] [NumberField F]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (s : Field.absoluteGaloisGroup F →ₜ* Q) (v : HeightOneSpectrum (𝓞 F))
    (hs : ∀ σ : finitePlaceAbsoluteInertiaSubgroup F v,
      s (finitePlaceAbsoluteDecompositionInclusion F v
        (finitePlaceAbsoluteInertiaInclusion F v σ)) = 1) :
    ChosenFinitePlaceIsUnramified (K := F) (L := absoluteDiscreteKernelField F s) v := by
  apply chosenFinitePlaceIsUnramified_of_absoluteInertiaFixes F
    (absoluteDiscreteKernelField F s) v
  intro σ x
  have hFixed : (σ.1.1 : Gal(AlgebraicClosure F/F)) ∈
      (absoluteDiscreteKernelField F s).fixingSubgroup := by
    rw [absoluteDiscreteKernelField_fixingSubgroup]
    exact hs σ
  exact hFixed x

end KernelLocalization

private theorem discreteKernel_eq_one_of_fixes
    (F : Type) [Field F] [NumberField F]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (s : Field.absoluteGaloisGroup F →ₜ* Q) (σ : Field.absoluteGaloisGroup F)
    (hFix : ∀ x : absoluteDiscreteKernelField F s,
      (absoluteGaloisGroupContinuousMulEquiv F σ) (x : AlgebraicClosure F) = x) :
    s σ = 1 := by
  have hFixed : (absoluteGaloisGroupContinuousMulEquiv F σ) ∈
      (absoluteDiscreteKernelField F s).fixingSubgroup := hFix
  rw [absoluteDiscreteKernelField_fixingSubgroup] at hFixed
  exact hFixed

/-- Killing the specified finite inertia gives a
continuous factor through the actual maximal pro-p extension. -/
theorem exists_maximalProPOutside_factor_of_inertia_trivial
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (hP : IsPGroup p Q) (s : Field.absoluteGaloisGroup ℚ →ₜ* Q)
    (hs : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ T →
      ∀ σ : finitePlaceAbsoluteInertiaSubgroup ℚ v,
        s (finitePlaceAbsoluteDecompositionInclusion ℚ v
          (finitePlaceAbsoluteInertiaInclusion ℚ v σ)) = 1) :
    ∃ t : (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T) →ₜ* Q,
      t.comp (absoluteToMaximalProPOutside p T) = s := by
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := absoluteDiscreteKernelField ℚ s
  let : IsGalois ℚ M := absoluteDiscreteKernelField_isGalois ℚ s
  let : NumberField M := NumberField.of_module_finite ℚ M
  have hPM : IsPGroup p (M ≃ₐ[ℚ] M) :=
    absoluteDiscreteKernelField_isPGroup ℚ s p hP
  have hFinite : IsUnramifiedAtFinitePlacesOutside ℚ M T := by
    intro P hPOutside
    apply isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
      (finitePlaceBelow (K := ℚ) P) P rfl
    exact discreteKernel_chosenUnramified ℚ s (finitePlaceBelow (K := ℚ) P)
      (hs (finitePlaceBelow (K := ℚ) P) hPOutside)
  let E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    { toIntermediateField := M
      finiteDimensional := inferInstance
      isGalois := absoluteDiscreteKernelField_isGalois ℚ s }
  have hM : M ≤ maximalProPOutside p T :=
    le_maximalProPOutside ⟨E, hPM, hFinite⟩
  have hKer : (absoluteToMaximalProPOutside p T).toMonoidHom.ker ≤
      s.toMonoidHom.ker := by
    intro σ hσ
    rw [absoluteToMaximalProPOutside_ker] at hσ
    apply discreteKernel_eq_one_of_fixes ℚ s σ
    intro x
    exact hσ ⟨x, hM x.property⟩
  let q : (Field.absoluteGaloisGroup ℚ ⧸
      (absoluteToMaximalProPOutside p T).toMonoidHom.ker) →ₜ* Q :=
    ProCGroups.QuotientGroup.liftₜ
      (absoluteToMaximalProPOutside p T).toMonoidHom.ker s hKer
  let e := absoluteProPOutsideQuotientEquiv p T
  refine ⟨q.comp e.symm, ?_⟩
  ext σ
  change q (e.symm (absoluteToMaximalProPOutside p T σ)) = s σ
  rw [← absoluteProPOutsideQuotientEquiv_mk p T σ, e.symm_apply_apply]
  exact ProCGroups.QuotientGroup.liftₜ_apply_mk
    (absoluteToMaximalProPOutside p T).toMonoidHom.ker s hKer σ

end UnitDistance.ArithmeticProP
