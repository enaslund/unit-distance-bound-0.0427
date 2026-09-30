/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquiv
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInclusion

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Compatibility of the chosen integral equivalence and inclusion

This file compares the integral-block inclusion with the finite-place tensor
equivalence on underlying field units.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

omit [NumberField L] in
/-- The integral-block inclusion is compatible with the pre-existing
local-block equivalence on underlying field units. -/
theorem
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_equiv_apply
    (w₀ : HeightOneSpectrum (𝓞 K))
    (x : relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w₀) :
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
        (K := K) (L := L) w₀
        (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
          (K := K) (L := L) w₀ x) =
      finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (x : (w₀.adicCompletion K ⊗[K] L)ˣ) := by
  let vK := HeightOneSpectrum.adicAbv K w₀
  let u := chosenFinitePlaceExtension (L := L) w₀
  let hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial w₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K w₀
  let := decompositionGroupLocalUnitsAction vK hvK u
  apply
    (inducedRightCosetCoordinates
      (absoluteValueDecompositionGroup K u.1)).injective
  funext q
  apply Units.ext
  rfl
end ChosenFinitePlace
