/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInclusion

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Equivariance of the induced integral block

This file proves that the inclusion of the chosen integral induced block is
equivariant for the global Galois action.
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
/-- The embedding of the chosen integral induced block is equivariant for
the full global Galois action. -/
theorem chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_smul
    (w₀ : HeightOneSpectrum (𝓞 K))
    (τ : L ≃ₐ[K] L) :
    ∀ f : ChosenFinitePlaceInducedIntegerUnits
        (K := K) (L := L) w₀,
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
        (K := K) (L := L) w₀
        ((chosenFinitePlaceInducedIntegerUnitsAction
          (K := K) (L := L) w₀).smul τ f) =
      (chosenFinitePlaceLocalPlaceBlockAction
        (K := K) (L := L) w₀).smul τ
        (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
          (K := K) (L := L) w₀ f) := by
  intro f
  rfl

end ChosenFinitePlace
