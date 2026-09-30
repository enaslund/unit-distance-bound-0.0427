module

public import UnitDistance.SIntegerFiberSum
public import UnitDistance.RelativeFieldProfile

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual finite-place and archimedean weighted S-integer estimate

Every finite-place coset is an actual period-ideal fiber. The proved uniform
Poisson estimate bounds that fiber, and the disjoint local cosets are bounded
by the actual local integral. The ideal norm cancels the exact finite-period
Haar volume, leaving the ordinary S-adic discriminant covolume.
-/

noncomputable section
open Set MeasureTheory NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors
namespace UnitDistance.RelativeUnits
open SIntegerCRT

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]
  {T : Type*} [Fintype T]

local instance localMeasurableSpace (P : T → HeightOneSpectrum (𝓞 K)) (t : T) :
    MeasurableSpace ((P t).adicCompletion K) := borel ((P t).adicCompletion K)
local instance localBorelSpace (P : T → HeightOneSpectrum (𝓞 K)) (t : T) :
    BorelSpace ((P t).adicCompletion K) := ⟨rfl⟩

/-- The finite-place profile is arbitrary subject to its ordinary proved
regularity and period properties. All arithmetic lattice and Fourier data
are the actual data of the field and selected primes. -/
theorem sInteger_relativeProfile_sum_le
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (P : T → HeightOneSpectrum (𝓞 K)) (hP : Function.Injective P) (a : T → ℤ)
    (hgap : Real.log 2+2*Real.log 5+2 ≤ EuclideanIdeal.dualScale K (periodIdeal P a))
    (g : LocalProduct P → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hgi : Integrable g (localProductHaar P))
    (hgperiod : ∀ z ∈ finitePeriod P a, ∀ x, g (x+z) = g x)
    (h : PairPlaceIndex F → ℝ) (r : EuclideanIdeal.Space K) (t : LocalProduct P)
    (s : Finset ((Set.range P).integer K)) :
    (∑ x ∈ s, relativeProfile ι hι
      (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
        (r+EuclideanIdeal.embedding K x.val)) * g (localEmbedding P x.val+t)) ≤
      2*(Witness.compactMass^nrRealPlaces F*Witness.pairMass^nrComplexPlaces F)*
        (∫ y, g y ∂localProductHaar P) /
        ((2⁻¹ : ℝ)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  letI : (localProductHaar P).IsAddRightInvariant := by
    unfold localProductHaar
    infer_instance
  let I := periodIdeal P a
  let A := Witness.compactMass^nrRealPlaces F*Witness.pairMass^nrComplexPlaces F
  let D := (2⁻¹ : ℝ)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|
  let N := (FractionalIdeal.absNorm I.val : ℝ)
  let C := 2*A/(N*D)
  let f : EuclideanIdeal.Space K → ℝ := fun x =>
    relativeProfile ι hι (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h) x)
  have hf (r' : EuclideanIdeal.Space K) (s' : Finset (EuclideanIdeal.lattice K I)) :
      (∑ v ∈ s', f (r'+(v : EuclideanIdeal.Space K))) ≤ C := by
    simpa only [f, C, A, N, D, mul_assoc] using
      relativeProfile_pulledBack_ideal_sum_le ι hι I hgap h r' s'
  have hC : 0 ≤ C := by simpa using hf 0 ∅
  have hn : 0 < N := Rat.cast_pos.mpr (IdealMinimum.absNorm_pos K I I.ne_zero)
  have hb := finite_weighted_coset_sum_mul_measureReal_le (localProductHaar P)
    (finitePeriod P a) (finitePeriod_measurable P a) g hg0 hgi hgperiod s
    (fun x => localEmbedding P (x : K)+t)
    (fun x => f (r+EuclideanIdeal.embedding K (x : K))) C hC
    (sInteger_coset_archimedean_sum_le P hP a f C hC hf s r t)
  rw [finitePeriod_volume_eq_inv_norm] at hb
  change (∑ x ∈ s, f (r+EuclideanIdeal.embedding K (x : K))*
      g (localEmbedding P (x : K)+t))*N⁻¹ ≤ C*(∫ y, g y ∂localProductHaar P) at hb
  have hb' := mul_le_mul_of_nonneg_right hb hn.le
  rw [mul_assoc, inv_mul_cancel₀ hn.ne', mul_one] at hb'
  change _ ≤ 2*A*(∫ y, g y ∂localProductHaar P)/D
  have he : (C*(∫ y, g y ∂localProductHaar P))*N =
      2*A*(∫ y, g y ∂localProductHaar P)/D := by
    dsimp [C]
    field_simp
  exact hb'.trans_eq he

/-- Published period/discriminant thresholds discharge the scalar Fourier
separation in the actual S-integer weighted profile bound. -/
theorem sInteger_relativeProfile_sum_le_of_witness
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (P : T → HeightOneSpectrum (𝓞 K)) (hP : Function.Injective P) (a : T → ℤ)
    (hperiod : Witness.periodLogDensity ≤ EuclideanIdeal.logarithmicIdealDensity K (periodIdeal P a))
    (hdisc : EuclideanIdeal.logarithmicRootDiscriminant K ≤ Witness.logRD)
    (g : LocalProduct P → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hgi : Integrable g (localProductHaar P))
    (hgperiod : ∀ z ∈ finitePeriod P a, ∀ x, g (x+z) = g x)
    (h : PairPlaceIndex F → ℝ) (r : EuclideanIdeal.Space K) (t : LocalProduct P)
    (s : Finset ((Set.range P).integer K)) :
    (∑ x ∈ s, relativeProfile ι hι
      (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
        (r+EuclideanIdeal.embedding K x.val)) * g (localEmbedding P x.val+t)) ≤
      2*(Witness.compactMass^nrRealPlaces F*Witness.pairMass^nrComplexPlaces F)*
        (∫ y, g y ∂localProductHaar P) /
        ((2⁻¹ : ℝ)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  apply sInteger_relativeProfile_sum_le ι hι P hP a _ g hg0 hgi hgperiod h r t s
  rw [EuclideanIdeal.dualScale_eq_two_mul_exp]
  refine Witness.period_fourier_separation.trans ?_
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  linarith

end UnitDistance.RelativeUnits
