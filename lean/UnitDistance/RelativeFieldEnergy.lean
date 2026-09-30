module

public import UnitDistance.RelativeFieldProfile
public import UnitDistance.TensorEnergy

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual field energy and relative deformation windows

The energy uses the actual singleton/pair grouping of the quadratic field.
Its exponential is exactly the previously bounded field profile. The true
common window and all its relative deformations are compact.
-/

noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory
open scoped Classical
namespace UnitDistance.RelativeUnits
variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

def relativeEnergy (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (x : EuclideanIdeal.Space K) : ℝ :=
  Witness.tensorPositionEnergy
    (EuclideanIdeal.tensorCoordinates K (relativePlaceGrouping ι hι) x)

theorem relativeEnergy_weight_p (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (x : EuclideanIdeal.Space K) :
    Real.exp (-Witness.p*relativeEnergy ι hι x) = relativeProfile ι hι x :=
  Witness.tensorPositionEnergy_weight_p _

theorem continuous_relativeEnergy (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Continuous (relativeEnergy ι hι) :=
  Witness.continuous_tensorPositionEnergy.comp
    (EuclideanIdeal.tensorCoordinates K (relativePlaceGrouping ι hι)).continuous

@[simp] theorem relativeEnergy_neg (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (x : EuclideanIdeal.Space K) : relativeEnergy ι hι (-x) = relativeEnergy ι hι x := by
  simp only [relativeEnergy, map_neg, Witness.tensorPositionEnergy_neg]

theorem isCompact_relativeEnergy_window (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (T : ℝ) :
    IsCompact (energyWindow (relativeEnergy ι hι) T) :=
  (EuclideanIdeal.tensorCoordinates K (relativePlaceGrouping ι hι)).toHomeomorph.isCompact_preimage.mpr
    (Witness.isCompact_tensorPositionEnergy_window T)

theorem continuous_reciprocalLogScale (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Continuous (reciprocalLogScale ι hι) := by
  apply continuous_pi
  intro w
  unfold reciprocalLogScale
  cases relativePlaceGrouping ι hι w with
  | inl v => exact continuous_const
  | inr v =>
    cases v with
    | inl v => exact (continuous_apply v).neg
    | inr v => exact continuous_apply v

/-- The deformation is jointly continuous in all relative logs and positions. -/
theorem continuous_reciprocalDeformation (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Continuous (fun hx : (PairPlaceIndex F → ℝ) × EuclideanIdeal.Space K =>
      EuclideanIdeal.deformation K (reciprocalLogScale ι hι hx.1) hx.2) := by
  have hc : Continuous (fun hx : (PairPlaceIndex F → ℝ) × EuclideanIdeal.Space K =>
      ((EuclideanIdeal.coordinates K hx.2).1,
        fun w => Real.exp (reciprocalLogScale ι hι hx.1 w) •
          (EuclideanIdeal.coordinates K hx.2).2 w)) := by
    refine (((EuclideanIdeal.coordinates K).continuous.comp continuous_snd).fst).prodMk ?_
    apply continuous_pi
    intro w
    exact (Real.continuous_exp.comp ((continuous_apply w).comp
      ((continuous_reciprocalLogScale ι hι).comp continuous_fst))).smul
        ((continuous_apply w).comp
          (((EuclideanIdeal.coordinates K).continuous.comp continuous_snd).snd))
  have he (hx : (PairPlaceIndex F → ℝ) × EuclideanIdeal.Space K) :
      EuclideanIdeal.deformation K (reciprocalLogScale ι hι hx.1) hx.2 =
        (EuclideanIdeal.coordinates K).symm
          ((EuclideanIdeal.coordinates K hx.2).1,
            fun w => Real.exp (reciprocalLogScale ι hι hx.1 w) •
              (EuclideanIdeal.coordinates K hx.2).2 w) := by
    apply (EuclideanIdeal.coordinates K).injective
    rw [EuclideanIdeal.coordinates_deformation, ContinuousLinearEquiv.apply_symm_apply]
  simp_rw [he]
  exact (EuclideanIdeal.coordinates K).symm.continuous.comp hc

def deformedRelativeEnergy (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (h : PairPlaceIndex F → ℝ) (x : EuclideanIdeal.Space K) : ℝ :=
  relativeEnergy ι hι (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h) x)

theorem continuous_deformedRelativeEnergy (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Continuous (fun hx : (PairPlaceIndex F → ℝ) × EuclideanIdeal.Space K =>
      deformedRelativeEnergy ι hι hx.1 hx.2) :=
  (continuous_relativeEnergy ι hι).comp (continuous_reciprocalDeformation ι hι)

theorem isCompact_deformedRelativeEnergy_window (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (h : PairPlaceIndex F → ℝ) (T : ℝ) :
    IsCompact (energyWindow (deformedRelativeEnergy ι hι h) T) :=
  (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)).toHomeomorph.isCompact_preimage.mpr
    (isCompact_relativeEnergy_window ι hι T)

end UnitDistance.RelativeUnits
