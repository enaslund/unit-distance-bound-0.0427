/-
Retyped from `UnitDistance/AbsoluteProPFactor.lean` (adapted from Naganori
Yamaguchi, SawinTotallyRealTowers, commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4,
Apache-2.0; source AbsoluteRealProPFactor.lean): ℚ is replaced by an
arbitrary number field `F`.
-/
module

public import UnitDistance.Sqrt241.ProP.AbsoluteProPRestriction
public import UnitDistance.Sqrt241.ProP.FinitePExtension
public import UnitDistance.Sqrt241.ProP.MaximalProPOutside
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
# Factoring representations through the maximal pro-p compositum over `F`

A discrete p-group representation of the absolute Galois group of `F` killing
finite inertia outside `T` has an actual finite Galois kernel field satisfying
the defining local conditions. Its inclusion in the constructed compositum
gives a continuous factorization through restriction.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.ProP

open ClassFieldTower.Sawin ClassFieldTower.Martinet.Shafarevich

section KernelLocalization

local instance kernelLocalizationGalois
    (F : Type) [Field F] [NumberField F]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (s : Field.absoluteGaloisGroup F →ₜ* Q) :
    IsGalois F (absoluteDiscreteKernelField F s) :=
  absoluteDiscreteKernelField_isGalois F s

/-- The kernel field of a discrete representation killing inertia at `v` is
unramified at the chosen place above `v`. -/
theorem discreteKernel_chosenUnramified
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

theorem discreteKernel_eq_one_of_fixes
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

variable (F : Type) [Field F] [NumberField F]

/-- Killing the specified finite inertia gives a continuous factor through
the maximal pro-p extension of `F` unramified outside `T`. -/
theorem exists_maximalProPOutside_factor_of_inertia_trivial
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (hP : IsPGroup p Q) (s : Field.absoluteGaloisGroup F →ₜ* Q)
    (hs : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T →
      ∀ σ : finitePlaceAbsoluteInertiaSubgroup F v,
        s (finitePlaceAbsoluteDecompositionInclusion F v
          (finitePlaceAbsoluteInertiaInclusion F v σ)) = 1) :
    ∃ t : (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) →ₜ* Q,
      t.comp (absoluteToMaximalProPOutside F p T) = s := by
  let M : IntermediateField F (AlgebraicClosure F) := absoluteDiscreteKernelField F s
  let : IsGalois F M := absoluteDiscreteKernelField_isGalois F s
  let : NumberField M := NumberField.of_module_finite F M
  have hPM : IsPGroup p (M ≃ₐ[F] M) :=
    absoluteDiscreteKernelField_isPGroup F s p hP
  have hFinite : IsUnramifiedAtFinitePlacesOutside F M T := by
    intro P hPOutside
    apply isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
      (finitePlaceBelow (K := F) P) P rfl
    exact discreteKernel_chosenUnramified F s (finitePlaceBelow (K := F) P)
      (hs (finitePlaceBelow (K := F) P) hPOutside)
  let E : FiniteGaloisIntermediateField F (AlgebraicClosure F) :=
    { toIntermediateField := M
      finiteDimensional := inferInstance
      isGalois := absoluteDiscreteKernelField_isGalois F s }
  have hM : M ≤ maximalProPOutside F p T :=
    le_maximalProPOutside ⟨E, hPM, hFinite⟩
  have hKer : (absoluteToMaximalProPOutside F p T).toMonoidHom.ker ≤
      s.toMonoidHom.ker := by
    intro σ hσ
    rw [absoluteToMaximalProPOutside_ker] at hσ
    apply discreteKernel_eq_one_of_fixes F s σ
    intro x
    exact hσ ⟨x, hM x.property⟩
  let q : (Field.absoluteGaloisGroup F ⧸
      (absoluteToMaximalProPOutside F p T).toMonoidHom.ker) →ₜ* Q :=
    ProCGroups.QuotientGroup.liftₜ
      (absoluteToMaximalProPOutside F p T).toMonoidHom.ker s hKer
  let e := absoluteProPOutsideQuotientEquiv F p T
  refine ⟨q.comp e.symm, ?_⟩
  ext σ
  change q (e.symm (absoluteToMaximalProPOutside F p T σ)) = s σ
  rw [← absoluteProPOutsideQuotientEquiv_mk F p T σ, e.symm_apply_apply]
  exact ProCGroups.QuotientGroup.liftₜ_apply_mk
    (absoluteToMaximalProPOutside F p T).toMonoidHom.ker s hKer σ

end UnitDistance.Sqrt241.ProP
