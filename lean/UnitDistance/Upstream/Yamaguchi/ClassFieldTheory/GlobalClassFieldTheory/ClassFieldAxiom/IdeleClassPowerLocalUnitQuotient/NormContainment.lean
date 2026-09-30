/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitNormContainment
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlace
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceAction
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlock
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquiv
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquivApply
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInclusion
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInducedSmul
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockTensorSmul
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.CompletionTransport
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Spine
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Action
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Equiv
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Inclusion

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Norm containment for idele power-local-unit subgroups

This file proves that the concrete local-condition subgroup lies in the global
idele norm range, and descends that inclusion to idele classes.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The idele norm inclusion `h(S,T) ⊆ N_{L/K} I_L`. -/
theorem idelePowerLocalUnitSubgroup_le_relativeIdeleNorm_range
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (harch :
      Even (n : ℕ) ∨
        ∀ w : InfinitePlace K, ¬ w.IsReal)
    (hT :
      ∀ v, v ∈ T →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := L) v)
    (hAway :
      ∀ v, v ∉ S ∪ T →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := L) v) :
    idelePowerLocalUnitSubgroup (K := K) n S T ≤
      (RelativeIdeleGroup.norm K L).range := by
  intro a ha
  rw [_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms]
  constructor
  · intro w
    apply
      _root_.infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
        (K := K) (L := L) w
    apply
      nthPowerSubgroup_le_infinitePositiveSubgroup
        (K := K) n w
    · exact harch.imp_right (fun h => h w)
    · exact
        ((mem_idelePowerLocalUnitSubgroup_iff
          (K := K) n S T a).mp ha).1 w
  · intro v
    rw [
      _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
    have hall :=
      idelePowerLocalUnitSubgroup_le_allFinitePlaceLocalNormCondition
        (K := K) (L := L) n r eG S T hT hAway ha
    exact Subgroup.mem_iInf.mp hall v

/-- The induced norm inclusion on idele class groups:
`N_{L/K} C_L ⊇ C_K(S,T)`. -/
theorem ideleClassPowerLocalUnitSubgroup_le_ideleClassNorm_range
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (harch :
      Even (n : ℕ) ∨
        ∀ w : InfinitePlace K, ¬ w.IsReal)
    (hT :
      ∀ v, v ∈ T →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := L) v)
    (hAway :
      ∀ v, v ∉ S ∪ T →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := L) v) :
    ideleClassPowerLocalUnitSubgroup (K := K) n S T ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range := by
  rintro c ⟨a, ha, rfl⟩
  obtain ⟨b, hb⟩ :=
    idelePowerLocalUnitSubgroup_le_relativeIdeleNorm_range
      (K := K) (L := L) n r eG S T harch hT hAway ha
  refine
    ⟨QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) b, ?_⟩
  rw [RelativeIdeleGroup.Cohomology.ideleClassNorm_mk, hb]


end GlobalClassFieldTheory.ClassFieldAxiom
