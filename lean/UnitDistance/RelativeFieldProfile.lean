module

public import UnitDistance.RelativeArchimedeanCoordinates
public import UnitDistance.TensorFieldCoordinates
public import UnitDistance.DeformedIdealPullback
public import UnitDistance.IdealScale
public import UnitDistance.WitnessPeriodSeparation

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual quadratic field profile and its uniform weighted ideal sum

Both the place grouping and Fourier estimate are proved for the actual
Gaussian/Student witness. Only the explicit ideal-scale inequality remains
in the counting theorem, which holds for every relative deformation.
-/

noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors Classical FourierTransform
namespace UnitDistance.RelativeUnits
variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

/-- The actual p-th-power profile, with compact and paired blocks determined
by restriction of the field's infinite places. -/
def relativeProfile (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) : EuclideanIdeal.Space K → ℝ :=
  EuclideanIdeal.archimedeanProfile K (relativePlaceGrouping ι hι)

theorem relativeProfile_pos (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (x : EuclideanIdeal.Space K) : 0 < relativeProfile ι hι x :=
  EuclideanIdeal.archimedeanProfile_pos K _ x

theorem integrable_relativeProfile (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Integrable (relativeProfile ι hι) :=
  EuclideanIdeal.integrable_archimedeanProfile K _

theorem integral_relativeProfile (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    (∫ x, relativeProfile ι hι x) =
      Witness.compactMass ^ nrRealPlaces F * Witness.pairMass ^ nrComplexPlaces F :=
  EuclideanIdeal.integral_archimedeanProfile K _

theorem relativeProfile_fourier_envelope (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (ξ : EuclideanIdeal.Space K) :
    ‖𝓕 (fun x => (relativeProfile ι hι x : ℂ)) ξ‖ ≤
      ((∫ x, relativeProfile ι hι x)*2^nrComplexPlaces K)*
        Real.exp (-EuclideanIdeal.coordinateNorm K ξ) :=
  EuclideanIdeal.archimedeanProfile_fourier_envelope K _ ξ

/-- Every actual relative deformation and every translate have the same
weighted bound, with no Fourier, summability or approximation assumptions. -/
theorem relativeProfile_pulledBack_ideal_sum_le
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hgap : Real.log 2+2*Real.log 5+2 ≤ EuclideanIdeal.dualScale K I)
    (h : PairPlaceIndex F → ℝ) (r : EuclideanIdeal.Space K)
    (points : Finset (EuclideanIdeal.lattice K I)) :
    ∑ v ∈ points, relativeProfile ι hι
      (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
        (r+(v:EuclideanIdeal.Space K))) ≤
      2*(Witness.compactMass ^ nrRealPlaces F * Witness.pairMass ^ nrComplexPlaces F) /
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)*
          (2⁻¹)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  have hf := EuclideanIdeal.temperateGrowth_archimedeanProfile K (relativePlaceGrouping ι hι)
  have hA := EuclideanIdeal.integral_archimedeanProfile_pos K (relativePlaceGrouping ι hι)
  have hb := EuclideanIdeal.translated_pulledBack_ideal_sum_le_of_envelope
    K I (reciprocalLogScale ι hι h) (sum_reciprocalLogScale ι hι h)
    (f := relativeProfile ι hι) hf (fun x => (relativeProfile_pos ι hι x).le)
    (integrable_relativeProfile ι hι) hA (M := 2) (σ := 1)
    (by norm_num) (by norm_num) (by simpa only [one_mul] using hgap)
    (by simpa only [neg_one_mul] using relativeProfile_fourier_envelope ι hι) r points
  rwa [integral_relativeProfile] at hb

/-- Equivalent counting criterion in the manuscript's actual normalized
ideal norm and root-discriminant variables. -/
theorem relativeProfile_pulledBack_ideal_sum_le_of_log_scale
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hgap : Real.log 2+2*Real.log 5+2 ≤
      2*Real.exp (EuclideanIdeal.logarithmicIdealDensity K I/2-
        EuclideanIdeal.logarithmicRootDiscriminant K))
    (h : PairPlaceIndex F → ℝ) (r : EuclideanIdeal.Space K)
    (points : Finset (EuclideanIdeal.lattice K I)) :
    ∑ v ∈ points, relativeProfile ι hι
      (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
        (r+(v:EuclideanIdeal.Space K))) ≤
      2*(Witness.compactMass ^ nrRealPlaces F * Witness.pairMass ^ nrComplexPlaces F) /
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)*
          (2⁻¹)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  apply relativeProfile_pulledBack_ideal_sum_le ι hι I _ h r points
  rwa [EuclideanIdeal.dualScale_eq_two_mul_exp]

/-- For the published period density and root-discriminant bound the scalar
Fourier condition is itself proved. The hypotheses refer only to actual
arithmetic invariants of the field and ideal. -/
theorem relativeProfile_pulledBack_ideal_sum_le_of_witness
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hperiod : Witness.periodLogDensity ≤ EuclideanIdeal.logarithmicIdealDensity K I)
    (hdisc : EuclideanIdeal.logarithmicRootDiscriminant K ≤ Witness.logRD)
    (h : PairPlaceIndex F → ℝ) (r : EuclideanIdeal.Space K)
    (points : Finset (EuclideanIdeal.lattice K I)) :
    ∑ v ∈ points, relativeProfile ι hι
      (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
        (r+(v:EuclideanIdeal.Space K))) ≤
      2*(Witness.compactMass ^ nrRealPlaces F * Witness.pairMass ^ nrComplexPlaces F) /
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)*
          (2⁻¹)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  apply relativeProfile_pulledBack_ideal_sum_le_of_log_scale ι hι I _ h r points
  refine Witness.period_fourier_separation.trans ?_
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  linarith

end UnitDistance.RelativeUnits
