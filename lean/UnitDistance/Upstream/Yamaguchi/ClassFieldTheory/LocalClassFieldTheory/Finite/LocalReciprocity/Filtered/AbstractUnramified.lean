/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch. The Mathlib
4.35 Denumerable import relocation is recorded in
third-party/yamaguchi/lean-v4.35-migration.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Unramified
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.Arithmetic
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.ContinuousFieldUnitLog
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.DenominatorValuation
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.FieldUnitLogExtension
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpAdditivity
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpComposition
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.ExpConvergence
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCore
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoicePositions
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.PowerSeriesComposition
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ProductArgument
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.BasicFactors
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoiceCountSystem
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ExplicitChoiceCounts
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalProduct
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.Homomorphisms
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.InverseEstimates
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.LogConvergence
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitExp
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitLog
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.SeriesTerms
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.LogExpContinuity
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.PrincipalUnitExpLogEquiv
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Analytic.FieldUnitLogUniqueness
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.GroupTheory.ContinuousQuotientEquiv
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.GroupTheory.IntegerMultipleSubgroup
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.GroupTheory.PowerIndex
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.EqualCharacteristicLaurent
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicQp
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FiniteCoefficientLaurent
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNormBase
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitDecomposition
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.SeriesValuationEstimates
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuationUniformizer
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.UniformizerIntegerValuation
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.LocalFieldRangeRestriction
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuedExtensionUnitMap
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.WithZeroValuationTopology
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNorm
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNormEquiv
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.NormFiltration
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.Core
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitInverseLimitSurjectivity
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicLinearOfContinuous
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitFactors
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicModuleStructure
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.Core
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Quotients
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.IwasawaIndexing
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.IwasawaPrincipalUnits
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitStructure
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PowerIndex
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicPowerIndex
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitPowerIndexFormulas
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.Units
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicValuationComparison
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.AdditiveEquiv
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormSubgroupFunctoriality
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ProfiniteUnits
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.MultiplicativeDecomposition
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueUnits
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UniformizerPrincipalQuotient
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.ClosedAddSubgroup
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinPolynomial
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinRelation
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.Existence
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.IntegralClosure
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.IntegralTranslate
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.PrimeElement
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.RamificationIndex
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.ValuationRingEquiv
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.Cyclotomic.Unramified.ArithmeticFrobenius
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalFieldTheory.Padic.Cyclotomic.Unramified.CanonicalExtension
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.PrincipalUnits
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.UnitDecomposition
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.BaseChange
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.BaseChangeCore
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.BasicInvariants
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.Composition
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.Definitions
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.FiniteSupport
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.HenselReduction
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.HenselianAlgebraicExtension
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.MaximalResidue
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.MaximalSubextension
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.ResidueEmbedding
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.ResidueLifting
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Unramified.Separable
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NormUnits
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormContainment
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Core

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Abstract unramified fixed fields and ramification groups

This file transfers unramifiedness from the residue-degree datum on the
absolute Galois group to the concrete valuation on the corresponding finite
fixed field.  It is the bridge from the canonical abstract unramified
extensions used in finite local reciprocity to the upper ramification groups
used in the Hasse--Arf development.
-/

noncomputable section

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open LubinTate

open ClassFormation
open CyclicCohomology
open LocalClassFieldTheory
open LocalFieldTheory
open RamificationTheory
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped NNReal ValuativeRel

universe u

private theorem baseFixingExtensionSubgroup_index_eq_finrank
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E] :
    (extensionSubgroup
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E)
      (fixingSubgroupLeBase K Ω E)).index =
        Module.finrank K E := by
  let : Finite
      ((closedFixingSubgroup K Ω
          (⊥ : IntermediateField K Ω)).toSubgroup ⧸
        extensionSubgroup
          (closedFixingSubgroup K Ω
            (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω E)
          (fixingSubgroupLeBase K Ω E)) :=
    Finite.of_equiv (Gal(E / K))
      (baseFixingExtensionQuotientEquivGaloisGroup K Ω E).symm.toEquiv
  calc
    _ = Nat.card
        ((closedFixingSubgroup K Ω
            (⊥ : IntermediateField K Ω)).toSubgroup ⧸
          extensionSubgroup
            (closedFixingSubgroup K Ω
              (⊥ : IntermediateField K Ω))
            (closedFixingSubgroup K Ω E)
            (fixingSubgroupLeBase K Ω E)) :=
      Subgroup.index_eq_card _
    _ = Nat.card (Gal(E / K)) :=
      Nat.card_congr
        (baseFixingExtensionQuotientEquivGaloisGroup K Ω E).toEquiv
    _ = Module.finrank K E :=
      IsGalois.card_aut_eq_finrank K E

/-- For a field finite over the distinguished abstract base, the absolute
residue degree agrees with its relative residue degree over that base. -/
theorem finiteAbstractField_residueDegree_eq_relativeResidueDegree
    {G : Type u} [Group G] [TopologicalSpace G]
    (D : DegreeData G) (H : FiniteAbstractField G) :
    (H.residueDegree D : ℕ) =
      (H.toFiniteAbstractExtension.residueDegree D : ℕ) := by
  apply Nat.cast_injective (R := Cardinal)
  calc
    ((H.residueDegree D : ℕ) : Cardinal) =
        D.residueDegreeCardinal H.field := by
      exact
        (DegreeData.FiniteResidueAbstractField.residueDegreeCardinal_eq_coe
          (H.toFiniteResidueAbstractField D)).symm
    _ =
        (H.toFiniteAbstractExtension.toAbstractExtension
          |>.relativeResidueDegreeCardinal D) := by
      have h :=
        H.toFiniteAbstractExtension.toAbstractExtension
          |>.relativeResidueDegreeCardinal_mul_residueDegreeCardinal D
      have hbase :
          D.residueDegreeCardinal
              H.toFiniteAbstractExtension.toAbstractExtension.base = 1 := by
        change D.residueDegreeCardinal (baseField G) = 1
        exact D.residueDegreeCardinal_baseField
      rw [hbase, mul_one] at h
      exact h.symm
    _ =
        ((H.toFiniteAbstractExtension.residueDegree D : ℕ) : Cardinal) :=
      H.toFiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe D

/-- The degree of a normal finite abstract field is the ordinary degree of
its concrete fixed field in the chosen separable closure. -/
theorem finiteAbstractField_degree_eq_abstractFixedField_finrank
    (K : Type) [Field K]
    (H : FiniteAbstractField
      (Gal(SeparableClosure K / K)))
    (hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K / K))) H.field
        (le_baseField H.field)).Normal) :
    let E :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K E :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : IsGalois K E :=
      abstractFixedField_isGalois_of_base_normal K H.field hnormal
    (H.toFiniteAbstractExtension.degree : ℕ) =
      Module.finrank K E := by
  let E :=
    abstractFixedField K (SeparableClosure K) H.field
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K H.field hnormal
  calc
    (H.toFiniteAbstractExtension.degree : ℕ) =
        (extensionSubgroup
          (baseField (Gal(SeparableClosure K / K))) H.field
          (le_baseField H.field)).index :=
      H.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree.symm
    _ = H.field.toSubgroup.index := by
      symm
      rw [← Subgroup.relIndex_top_right]
      rfl
    _ = E.fixingSubgroup.index := by
      exact congrArg Subgroup.index
        (InfiniteGalois.fixingSubgroup_fixedField H.field).symm
    _ = Module.finrank K E :=
      (IntermediateField.finrank_eq_fixingSubgroup_index
        (SeparableClosure K) E).symm

set_option maxHeartbeats 1000000 in
/-- Abstract unramifiedness of a normal finite fixed field gives actual
unramifiedness for its canonical spectral valuation. -/
theorem abstractFixedField_isUnramifiedValuedExtension
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      (Gal(SeparableClosure K / K)))
    (hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K / K))) H.field
        (le_baseField H.field)).Normal)
    (hunramified :
      H.toFiniteAbstractExtension.IsUnramified
        (localResidueDatum K)) :
    let E :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K E :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : IsGalois K E :=
      abstractFixedField_isGalois_of_base_normal K H.field hnormal
    letI : NontriviallyNormedField K :=
      localFieldNontriviallyNormedField K
    letI : IsUltrametricDist K :=
      localFieldIsUltrametricDist K
    letI : CompleteSpace K := inferInstance
    letI : NontriviallyNormedField E :=
      finiteExtensionSpectralNormedField K E
    letI : ValuativeRel E :=
      finiteExtensionSpectralValuativeRel K E
    letI : IsNonarchimedeanLocalField E :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K E
    letI : Valuation.HasExtension
        (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
      finiteExtensionSpectralValuation_hasExtension K E
    letI : IsIntegralClosure 𝒪[E] 𝒪[K] E :=
      localCompleteDVF_integerRing_isIntegralClosure K E
    letI : Module.Finite 𝒪[K] 𝒪[E] :=
      localCompleteDVF_integerRing_moduleFinite K E
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      K E := by
  let E :=
    abstractFixedField K (SeparableClosure K) H.field
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K H.field hnormal

  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K :=
    localFieldIsUltrametricDist K
  let : CompleteSpace K := inferInstance
  let : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  let : ValuativeRel E :=
    finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let : Algebra.IsIntegral
      (ValuativeRel.valuation K).valuationSubring
      (ValuativeRel.valuation E).valuationSubring := by
    change Algebra.IsIntegral 𝒪[K] 𝒪[E]
    infer_instance
  let hIntegralClosure : IsIntegralClosure
      (ValuativeRel.valuation E).valuationSubring
      (ValuativeRel.valuation K).valuationSubring E :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_isIntegralClosure_of_isIntegral
      (ValuativeRel.valuation K) (ValuativeRel.valuation E)
  let : IsIntegralClosure 𝒪[E] 𝒪[K] E := by
    change IsIntegralClosure
      (ValuativeRel.valuation E).valuationSubring
      (ValuativeRel.valuation K).valuationSubring E
    exact hIntegralClosure
  let : Module.Finite 𝒪[K] 𝒪[E] :=
    localCompleteDVF_integerRing_moduleFinite K E

  letI : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let i : 𝒪[K] →+* 𝒪[E] :=
    integerRingMapOfValuationExtension K E
  let hi : IsLocalHom i :=
    Valuation.HasExtension.instIsLocalHomValuationInteger
      (vR := ValuativeRel.valuation K)
      (vS := ValuativeRel.valuation E)
  let integerAlgebra : Algebra 𝒪[K] 𝒪[E] :=
    Valuation.HasExtension.instAlgebraInteger
      (vR := ValuativeRel.valuation K)
      (vA := ValuativeRel.valuation E)
  have hiAlgebra : i.toAlgebra = integerAlgebra := by
    apply Algebra.algebra_ext
    intro r
    rfl
  letI : Algebra 𝒪[K] 𝒪[E] := integerAlgebra
  have hmap : (algebraMap 𝒪[K] 𝒪[E] : 𝒪[K] →+* 𝒪[E]) = i := by
    change integerAlgebra.algebraMap = i
    exact (congrArg
      (fun A : Algebra 𝒪[K] 𝒪[E] => A.algebraMap) hiAlgebra).symm
  letI : IsLocalHom (algebraMap 𝒪[K] 𝒪[E]) := by
    rw [hmap]
    exact hi
  let residueModule : Module 𝓀[K] 𝓀[E] :=
    @IsLocalRing.ResidueField.instModule 𝒪[K] 𝒪[E] _ _ _ _
      integerAlgebra hi
  let quotientResidueAlgebra : Algebra 𝓀[K] 𝓀[E] :=
    Ideal.Quotient.algebraOfLiesOver (𝓂[E] : Ideal 𝒪[E])
      (𝓂[K] : Ideal 𝒪[K])
  let theoremResidueModule : Module 𝓀[K] 𝓀[E] :=
    quotientResidueAlgebra.toModule
  have hdefaultResidueModule :
      theoremResidueModule = residueModule := by
    exact Module.ext' theoremResidueModule residueModule (by
      intro r x
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      dsimp only [theoremResidueModule, residueModule]
      all_goals rfl)
  let integralResidueAlgebra : Algebra 𝓀[K] 𝓀[E] :=
    IsLocalRing.ResidueField.algebraOfIsIntegral
      (R := 𝒪[K]) (k := 𝓀[E])
  let algebraModule : Module 𝓀[K] 𝓀[E] := integralResidueAlgebra.toModule
  have hresidueAlgebra : quotientResidueAlgebra = integralResidueAlgebra := by
    apply Algebra.algebra_ext
    intro r
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    calc
      quotientResidueAlgebra.algebraMap (IsLocalRing.residue 𝒪[K] r) =
          IsLocalRing.residue 𝒪[E] (algebraMap 𝒪[K] 𝒪[E] r) := by
        letI : Algebra 𝓀[K] 𝓀[E] := quotientResidueAlgebra
        exact IsLocalRing.ResidueField.algebraMap_residue r
      _ = integralResidueAlgebra.algebraMap (IsLocalRing.residue 𝒪[K] r) := by
        rfl
  have hresidueModule : residueModule = algebraModule := by
    calc
      residueModule = theoremResidueModule := hdefaultResidueModule.symm
      _ = quotientResidueAlgebra.toModule := rfl
      _ = integralResidueAlgebra.toModule :=
        congrArg (fun A : Algebra 𝓀[K] 𝓀[E] => A.toModule)
          hresidueAlgebra
      _ = algebraModule := rfl
  have hresidueFinrank := congrArg
    (fun M : Module 𝓀[K] 𝓀[E] =>
      @Module.finrank 𝓀[K] 𝓀[E] _ _ M) hresidueModule

  have hresidueDegreeQuotient :
      @Module.finrank 𝓀[K] 𝓀[E] _ _ residueModule = Module.finrank K E := by
    calc
      @Module.finrank 𝓀[K] 𝓀[E] _ _ residueModule =
          Module.finrank 𝓀[K] 𝓀[E] := by rw [hresidueModule]
      _ = (H.residueDegree (localResidueDatum K) : ℕ) :=
        by
          unfold algebraModule
          exact
            (localResidueDatum_residueDegree_eq_residueFinrank K H).symm
      _ =
          (H.toFiniteAbstractExtension.residueDegree
            (localResidueDatum K) : ℕ) :=
        finiteAbstractField_residueDegree_eq_relativeResidueDegree
          (localResidueDatum K) H
      _ = (H.toFiniteAbstractExtension.degree : ℕ) :=
        H.toFiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified
          (localResidueDatum K) hunramified
      _ = Module.finrank K E :=
        finiteAbstractField_degree_eq_abstractFixedField_finrank
          K H hnormal
  have hresidueDegree :
      Module.finrank 𝓀[K] 𝓀[E] = Module.finrank K E := by
    change @Module.finrank 𝓀[K] 𝓀[E] _ _ algebraModule = _
    rw [← hresidueModule]
    exact hresidueDegreeQuotient

  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  have hdegree :=
    maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure
      K E
  have hdegreeQuotient :
      (𝓂[K] : Ideal 𝒪[K]).ramificationIdx'
          (𝓂[E] : Ideal 𝒪[E]) *
        @Module.finrank 𝓀[K] 𝓀[E] _ _ residueModule =
          Module.finrank K E := by
    change (𝓂[K] : Ideal 𝒪[K]).ramificationIdx'
        (𝓂[E] : Ideal 𝒪[E]) *
      @Module.finrank 𝓀[K] 𝓀[E] _ _ theoremResidueModule =
        Module.finrank K E
    rw [hdefaultResidueModule]
    exact hdegree
  have hdegree' :
      (𝓂[E] : Ideal 𝒪[E]).ramificationIdx 𝒪[K] *
          Module.finrank 𝓀[K] 𝓀[E] =
        Module.finrank K E := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp]
    rw [← hresidueFinrank]
    exact hdegreeQuotient
  have hpos : 0 < Module.finrank 𝓀[K] 𝓀[E] :=
    Module.finrank_pos
  apply
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension.mk
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    (𝓂[E] : Ideal 𝒪[E]).ramificationIdx 𝒪[K] *
        Module.finrank 𝓀[K] 𝓀[E] =
      Module.finrank K E := hdegree'
    _ = Module.finrank 𝓀[K] 𝓀[E] := hresidueDegree.symm
    _ = 1 * Module.finrank 𝓀[K] 𝓀[E] := (one_mul _).symm

/-- Every nonnegative upper ramification group of an abstractly unramified
normal finite fixed field is trivial. -/
theorem localUpperRamificationGroup_abstractFixedField_eq_bot
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      (Gal(SeparableClosure K / K)))
    (hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K / K))) H.field
        (le_baseField H.field)).Normal)
    (hunramified :
      H.toFiniteAbstractExtension.IsUnramified
        (localResidueDatum K))
    (t : ℝ) (ht : 0 ≤ t) :
    let E :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K E :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : IsGalois K E :=
      abstractFixedField_isGalois_of_base_normal K H.field hnormal
    localUpperRamificationGroup K E t = ⊥ := by
  let E :=
    abstractFixedField K (SeparableClosure K) H.field
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K H.field hnormal

  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K :=
    localFieldIsUltrametricDist K
  let : CompleteSpace K := inferInstance
  let : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  let : ValuativeRel E :=
    finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let : IsIntegralClosure 𝒪[E] 𝒪[K] E :=
    localCompleteDVF_integerRing_isIntegralClosure K E
  let : Module.Finite 𝒪[K] 𝒪[E] :=
    localCompleteDVF_integerRing_moduleFinite K E
  let :
      LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        K E :=
    abstractFixedField_isUnramifiedValuedExtension
      K H hnormal hunramified
  exact
    localUpperRamificationGroup_eq_bot_of_unramifiedValuation
      K E t ht

/-! ## The canonical degree-`d` unramified factor -/

/-- The fixed-field endpoint of the canonical degree-`d` unramified
subextension, bundled as an abstract field finite over the distinguished
base. -/
noncomputable def localFiniteUnramifiedAbstractField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    FiniteAbstractField (intrinsicAbsoluteGalois K) := by
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  exact ⟨U.field,
    finiteAbelianSubextension_finite_over_absoluteBase K U⟩

/-- The preceding absolute finite-field package has the subgroup underlying
the canonical finite unramified abelian subextension. -/
@[simp]
theorem localFiniteUnramifiedAbstractField_field
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    (localFiniteUnramifiedAbstractField K d hd).field =
      (localFiniteUnramifiedAbelianSubextension K d hd).field := by
  rfl

/-- The canonical degree-`d` unramified abstract field is normal over the
distinguished base. -/
theorem localFiniteUnramifiedAbstractField_normal
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    (extensionSubgroup
      (baseField (intrinsicAbsoluteGalois K))
      (localFiniteUnramifiedAbstractField K d hd).field
    (le_baseField
        (localFiniteUnramifiedAbstractField K d hd).field)).Normal := by
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  change
    (extensionSubgroup
      (baseField (intrinsicAbsoluteGalois K)) U.field
      (le_baseField U.field)).Normal
  exact finiteAbelianSubextension_normal_over_absoluteBase K U

/-- The canonical degree-`d` abstract field is unramified for the local
residue degree datum. -/
theorem localFiniteUnramifiedAbstractField_isUnramified
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    (localFiniteUnramifiedAbstractField K d hd).toFiniteAbstractExtension.IsUnramified
      (localResidueDatum K) := by
  let D := localResidueDatum K
  let Bfinite : FiniteAbstractField (intrinsicAbsoluteGalois K) :=
    intrinsicFiniteAbstractBase K
  let Bresidue := Bfinite.toFiniteResidueAbstractField D
  have h :=
    DegreeData.unramifiedExtensionOfDegree_isUnramified
      D Bresidue d hd
  have hbase :
      intrinsicAbstractBase K =
        baseField (intrinsicAbsoluteGalois K) :=
    closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)
  change
    (baseField (intrinsicAbsoluteGalois K)).toSubgroup ⊓
        D.degree.toMonoidHom.ker ≤
      (localFiniteUnramifiedAbelianSubextension K d hd).field.toSubgroup
  intro g hg
  have hgBase : g ∈ Bresidue.field := by
    change g ∈ intrinsicAbstractBase K
    rw [hbase]
    exact hg.1
  have hgField :=
    h ⟨hgBase, hg.2⟩
  simpa [D, Bfinite, Bresidue,
    localFiniteUnramifiedAbelianSubextension,
    DegreeData.finiteUnramifiedAbelianExtension,
    DegreeData.finiteUnramifiedExtension] using hgField

/-- Every nonnegative upper ramification group of the canonical degree-`d`
unramified abelian fixed field is trivial. -/
theorem localUpperRamificationGroup_finiteUnramifiedAbelianExtension_eq_bot
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) (t : ℝ) (ht : 0 ≤ t) :
    let H := localFiniteUnramifiedAbstractField K d hd
    let E :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K E :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : IsGalois K E :=
      abstractFixedField_isGalois_of_base_normal K H.field
        (localFiniteUnramifiedAbstractField_normal K d hd)
    localUpperRamificationGroup K E t = ⊥ := by
  exact
    localUpperRamificationGroup_abstractFixedField_eq_bot
      K (localFiniteUnramifiedAbstractField K d hd)
        (localFiniteUnramifiedAbstractField_normal K d hd)
        (localFiniteUnramifiedAbstractField_isUnramified K d hd)
        t ht

/-- The real Artin principal-unit step filtration of the canonical
degree-`d` unramified abelian fixed field is trivial at every index. -/
theorem
    artinPrincipalUnitStepGroup_finiteUnramifiedAbelianExtension_eq_bot
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) (t : ℝ) :
    let H := localFiniteUnramifiedAbstractField K d hd
    let E :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K E :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : IsAbelianGalois K E := by
      change IsAbelianGalois K
        (abstractFixedField K (SeparableClosure K)
          (localFiniteUnramifiedAbelianSubextension K d hd).field)
      exact finiteAbelianSubextension_fixedField_isAbelianGalois K
        (localFiniteUnramifiedAbelianSubextension K d hd)
    artinPrincipalUnitStepGroup K E t = ⊥ := by
  let H := localFiniteUnramifiedAbstractField K d hd
  let E :=
    abstractFixedField K (SeparableClosure K) H.field
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : IsAbelianGalois K E := by
    change IsAbelianGalois K
      (abstractFixedField K (SeparableClosure K)
        (localFiniteUnramifiedAbelianSubextension K d hd).field)
    exact finiteAbelianSubextension_fixedField_isAbelianGalois K
      (localFiniteUnramifiedAbelianSubextension K d hd)

  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K :=
    localFieldIsUltrametricDist K
  let : CompleteSpace K := inferInstance
  let : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  let : ValuativeRel E :=
    finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let :
      LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        K E :=
    abstractFixedField_isUnramifiedValuedExtension
      K H
        (localFiniteUnramifiedAbstractField_normal K d hd)
        (localFiniteUnramifiedAbstractField_isUnramified K d hd)
  exact
    artinPrincipalUnitStepGroup_eq_bot_of_unramifiedValuation
      K E t

end LocalClassFieldTheory
