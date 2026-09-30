module

public import UnitDistance.StudentSchwartzApproximation
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual Euclidean coordinates for the Student Schwartz approximants

The space `WithLp 2 (ℂ × ℂ)` carries the Euclidean product norm, whose square
is exactly the sum of the two ordinary complex norm squares. Its canonical
Lebesgue measure maps to the original product complex Lebesgue measure.
Thus neither a new metric nor an assumed coordinate normalization is needed.
-/

open MeasureTheory Filter
open scoped Topology

namespace UnitDistance.Witness

abbrev StudentEuclideanPair := WithLp 2 (ℂ × ℂ)

noncomputable def studentPairCoordinates : StudentEuclideanPair ≃L[ℝ] (ℂ × ℂ) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ

theorem studentPairCoordinates_measurePreserving :
    MeasurePreserving studentPairCoordinates volume volume :=
  WithLp.volume_preserving_ofLp ℂ ℂ

theorem studentPairCoordinates_norm_sq (x : StudentEuclideanPair) :
    ‖x‖^2 = ‖(studentPairCoordinates x).1‖^2 + ‖(studentPairCoordinates x).2‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 x

/-- An actual sequence of Schwartz functions on Euclidean four-space, with
exactly the published Student weight in the two complex coordinates. -/
noncomputable def pairSchwartzApprox (n : ℕ) : SchwartzMap StudentEuclideanPair ℂ :=
  studentSchwartzApprox studentPairCoordinates.toContinuousLinearMap n

@[simp] theorem pairSchwartzApprox_apply (n : ℕ) (x : StudentEuclideanPair) :
    pairSchwartzApprox n x =
      ((pairProfile (WithLp.ofLp x)^p *
        Real.exp (-(1/((n:ℝ)+1))*(‖(WithLp.ofLp x).1‖^2 + ‖(WithLp.ofLp x).2‖^2))) : ℝ) := by
  rw [pairSchwartzApprox, studentSchwartzApprox_apply, studentPairCoordinates_norm_sq]
  rfl

theorem pairSchwartzApprox_nonneg (n : ℕ) (x : StudentEuclideanPair) :
    0 ≤ (pairSchwartzApprox n x).re :=
  studentSchwartzApprox_nonneg studentPairCoordinates.toContinuousLinearMap n x

theorem pairSchwartzApprox_tendsto (x : StudentEuclideanPair) :
    Tendsto (fun n => (pairSchwartzApprox n x).re) atTop (𝓝 (pairProfile (WithLp.ofLp x)^p)) :=
  studentSchwartzApprox_tendsto studentPairCoordinates.toContinuousLinearMap x

theorem pairSchwartzApprox_mass_tendsto :
    Tendsto (fun n => ∫ x, (pairSchwartzApprox n x).re) atTop (𝓝 pairMass) :=
  studentSchwartzApprox_mass_tendsto studentPairCoordinates studentPairCoordinates_measurePreserving

/-- The remaining hypothesis is only the eventually valid bound for the
actual nonzero dual Fourier mass. All approximation and coordinate inputs
have been discharged for the actual four-dimensional Student block. -/
theorem pair_poisson_weighted_sum_le
    (L : Submodule ℤ StudentEuclideanPair) [DiscreteTopology L] [IsZLattice ℝ L]
    (hTail : ∀ᶠ n in atTop, nonzeroFourierMass L (pairSchwartzApprox n) ≤
      ∫ x, (pairSchwartzApprox n x).re)
    (r : StudentEuclideanPair) (points : Finset L) :
    ∑ v ∈ points, pairProfile (WithLp.ofLp (r+(v : StudentEuclideanPair)))^p ≤ 2*pairMass / ZLattice.covolume L :=
  student_poisson_weighted_sum_le L studentPairCoordinates studentPairCoordinates_measurePreserving
    hTail r points

end UnitDistance.Witness
