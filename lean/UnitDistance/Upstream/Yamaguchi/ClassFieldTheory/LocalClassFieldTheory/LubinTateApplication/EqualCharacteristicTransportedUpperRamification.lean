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

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LaurentPrincipalUnitTransport
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.LocalField.BaseChange
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedLevel
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedPrimitiveAction
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedPolynomialEvaluation
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizerNormalization
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusBaseEquiv
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusContinuity
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldAlgebra
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldCoefficientDescent
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldDegree
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldGeneration
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPowerBasis
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPrimitive
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusLift
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedNorm
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectBracketAtCompletedLevel
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracket
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracketRecursion
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectTargetLevelEmbedding
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaAtCompletedLevel
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFirstIdentity
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFrobeniusFixed
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaIteration
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaSeries
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaAtCompletedLevel
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaLocalInverse
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.AmbientBracketAction
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.DivisionModuleEndomorphisms
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateEndomorphism
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.ContractingEquation
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaCoefficients
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaEvaluation
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaUniqueness
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.RealIndexSteps
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.Core

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Upper ramification groups on transported equal-characteristic levels

The explicit Lubin--Tate level field is unchanged when its Laurent-series
base algebra is transported to an arbitrary equal-characteristic local
field.  The normalized Laurent equivalence preserves the valuation rings,
so the general base-field transport theorem identifies the two upper
ramification filtrations.
-/

noncomputable section

open scoped LaurentSeries ValuativeRel

namespace LubinTate

open LocalFieldTheory
open RamificationTheory.LocalField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate.EqualCharacteristic

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The two algebra maps from the Laurent model and the target local field
to a transported Lubin--Tate level have the same image. -/
theorem equalCharacteristicTransportedLubinTate_algebraMap_compat
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ)
    (x :
      let F := equalCharacteristicTargetLocalField K
      F.residueField⸨X⸩) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    algebraMap K E
        (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ x) =
      algebraMap B E x := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F n
  let : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  have hcomp :=
    DFunLike.congr_fun
      (equalCharacteristicTransportedLubinTateLevelAlgebra_comp
        K p ϖ hϖ n) x
  simpa using hcomp

/-- Identification of the Galois group over the Laurent base with the
Galois group for the transported target-field algebra.  It leaves every
underlying automorphism of the level field unchanged. -/
noncomputable def equalCharacteristicTransportedLubinTateGaloisEquiv
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    Gal(E / B) ≃* Gal(E / K) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F n
  letI : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F n
  letI : CharP K p := hKp
  letI : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  exact
    galoisGroupEquivOfBaseRingEquiv B K E
      (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ)
      (equalCharacteristicTransportedLubinTate_algebraMap_compat
        K p ϖ hϖ n)

@[simp]
theorem equalCharacteristicTransportedLubinTateGaloisEquiv_apply
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ)
    (σ :
      let F := equalCharacteristicTargetLocalField K
      let B := F.residueField⸨X⸩
      letI : CharP K F.residueCharacteristic :=
        equalCharacteristicTargetResidueCharacteristicCharP K p
      let E := equalCharacteristicLubinTateLevelField F n
      letI : Algebra B E :=
        equalCharacteristicLubinTateLevelAlgebra F n
      Gal(E / B))
    (x :
      let F := equalCharacteristicTargetLocalField K
      letI : CharP K F.residueCharacteristic :=
        equalCharacteristicTargetResidueCharacteristicCharP K p
      equalCharacteristicLubinTateLevelField F n) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    equalCharacteristicTransportedLubinTateGaloisEquiv
        K p ϖ hϖ n σ x =
      σ x := by
  rfl

private theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_baseChange
    [Fact
      (equalCharacteristicTargetLocalField K).residueCharacteristic.Prime]
    [CharP K
      (equalCharacteristicTargetLocalField K).residueCharacteristic]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) :
    let F := equalCharacteristicTargetLocalField K
    let q := F.residueCharacteristic
    let B := F.residueField⸨X⸩
    let E := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI algBE : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI finBE : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    letI galBE : IsGalois B E :=
      equalCharacteristicLubinTateLevelField_isGalois F n
    let upperB :=
      @localUpperRamificationGroup B E
        inferInstance inferInstance
        algBE finBE galBE
        inferInstance inferInstance inferInstance
    letI algKE : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K q ϖ hϖ n
    letI finKE : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K q ϖ hϖ n
    letI galKE : IsGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K q ϖ hϖ n
    let upperK :=
      @localUpperRamificationGroup K E
        inferInstance inferInstance
        algKE finKE galKE
        inferInstance inferInstance inferInstance
    Subgroup.map
        (@galoisGroupEquivOfBaseRingEquiv
          B K E
          inferInstance inferInstance inferInstance
          algBE algKE
          (equalCharacteristicTargetLaurentRingEquiv K q ϖ hϖ)
          (equalCharacteristicTransportedLubinTate_algebraMap_compat
            K q ϖ hϖ n)).toMonoidHom
        (upperB t) =
      upperK t := by
  let F := equalCharacteristicTargetLocalField K
  let q := F.residueCharacteristic
  let B := F.residueField⸨X⸩
  let E := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B :=
    equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let algBE : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let finBE : FiniteDimensional B E :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let galBE : IsGalois B E :=
    equalCharacteristicLubinTateLevelField_isGalois F n
  let algKE : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K q ϖ hϖ n
  let finKE : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K q ϖ hϖ n
  let galKE : IsGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isGalois
      K q ϖ hϖ n
  dsimp only
  convert
    @localUpperRamificationGroup_map_baseRingEquiv
      B K E
      inferInstance inferInstance inferInstance
      algBE algKE finBE finKE galBE galKE
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      (equalCharacteristicTargetLaurentRingEquiv K q ϖ hϖ)
      (equalCharacteristicTransportedLubinTate_algebraMap_compat
        K q ϖ hϖ n)
      (equalCharacteristicTargetLaurentRingEquiv_val_le_one_iff
        K q ϖ hϖ) t using 1

private theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_residueCharacteristic
    [Fact
      (equalCharacteristicTargetLocalField K).residueCharacteristic.Prime]
    [CharP K
      (equalCharacteristicTargetLocalField K).residueCharacteristic]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) :
    let F := equalCharacteristicTargetLocalField K
    let q := F.residueCharacteristic
    let B := F.residueField⸨X⸩
    let E := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI algBE : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI finBE : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    letI galBE : IsGalois B E :=
      equalCharacteristicLubinTateLevelField_isGalois F n
    let upperB :=
      @localUpperRamificationGroup B E
        (by infer_instance) (by infer_instance)
        algBE finBE galBE
        (by infer_instance) (by infer_instance) (by infer_instance)
    letI algKE : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K q ϖ hϖ n
    letI finKE : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K q ϖ hϖ n
    letI galKE : IsGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K q ϖ hϖ n
    let upperK :=
      @localUpperRamificationGroup K E
        (by infer_instance) (by infer_instance)
        algKE finKE galKE
        (by infer_instance) (by infer_instance) (by infer_instance)
    Subgroup.map
        (equalCharacteristicTransportedLubinTateGaloisEquiv
          K q ϖ hϖ n).toMonoidHom
        (upperB t) =
      upperK t := by
  simpa only [equalCharacteristicTransportedLubinTateGaloisEquiv] using
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_baseChange
      K ϖ hϖ n t

/-- The normalized base-field equivalence transports the canonical local
upper ramification group on every explicit Lubin--Tate level. -/
theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    let upperB := localUpperRamificationGroup B E
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p (hKp := hKp) ϖ hϖ n
    letI : Module K E := Algebra.toModule
    letI : IsGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K p (hKp := hKp) ϖ hϖ n
    letI : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p (hKp := hKp) ϖ hϖ n
    let upperK := localUpperRamificationGroup K E
    Subgroup.map
        (equalCharacteristicTransportedLubinTateGaloisEquiv
          K p (hKp := hKp) ϖ hϖ n).toMonoidHom
        (upperB t) =
      upperK t := by
  let F := equalCharacteristicTargetLocalField K
  have hp : F.residueCharacteristic = p :=
    F.residueCharacteristic_eq_of_charP p
      ((Fact.out : Nat.Prime p).ne_zero)
  subst p
  convert
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_residueCharacteristic
      K ϖ hϖ n t using 1

end LubinTate
