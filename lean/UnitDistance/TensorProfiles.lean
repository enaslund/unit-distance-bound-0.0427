module

public import UnitDistance.EndpointSymmetry
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
set_option backward.privateInPublic true


/-!
# Tensor overlap laws

These identities connect sums of endpoint energies with products of their
actual overlap measures. Independence across blocks is proved from the
product measure, and need not be supplied as an additional hypothesis.
The base measure of each block may already be restricted to profile support.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace UnitDistance

section ProductDensity

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}
  [∀ i, MeasurableSpace (Ω i)]

/-- Finite products commute with nonnegative integrable densities. -/
theorem pi_withDensity_ofReal (m : (i : ι) → Measure (Ω i)) [∀ i, SigmaFinite (m i)]
    (f : (i : ι) → Ω i → ℝ) (hf : ∀ i, Integrable (f i) (m i))
    (hnonneg : ∀ i x, 0 ≤ f i x) :
    (Measure.pi m).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) =
      Measure.pi (fun i => (m i).withDensity (fun x => ENNReal.ofReal (f i x))) := by
  letI (i : ι) : IsFiniteMeasure ((m i).withDensity (fun x => ENNReal.ofReal (f i x))) :=
    isFiniteMeasure_withDensity (by
      rw [← ofReal_integral_eq_lintegral_ofReal (hf i)
        (Filter.Eventually.of_forall (hnonneg i))]
      exact ENNReal.ofReal_ne_top)
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf).integrableOn
      (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hnonneg i (x i)))),
    Measure.restrict_pi_pi, integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnonneg i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i),
    ← ofReal_integral_eq_lintegral_ofReal (hf i).integrableOn
      (Filter.Eventually.of_forall (hnonneg i))]

def tensorEnergy (E : (i : ι) → Ω i → ℝ) (x : (i : ι) → Ω i) : ℝ :=
  ∑ i, E i (x i)

/-- Exact normalization and factorization of an overlap law. -/
theorem tensor_overlapLaw (m : (i : ι) → Measure (Ω i)) [∀ i, SigmaFinite (m i)]
    (X Y : (i : ι) → Ω i → ℝ) (Z : ι → ℝ)
    (hZ : ∀ i, 0 < Z i)
    (hI : ∀ i, Integrable (fun x => Real.exp (-(X i x + Y i x))) (m i)) :
    overlapLaw (Measure.pi m) (tensorEnergy X) (tensorEnergy Y) (∏ i, Z i) =
      Measure.pi (fun i => overlapLaw (m i) (X i) (Y i) (Z i)) := by
  have h := pi_withDensity_ofReal m
    (fun i x => Real.exp (-(X i x + Y i x)) / Z i)
    (fun i => (hI i).div_const (Z i))
    (fun i x => div_nonneg (Real.exp_pos _).le (hZ i).le)
  simp only [overlapLaw] at h ⊢
  rw [← h]
  congr 1
  funext x
  congr 1
  rw [Finset.prod_div_distrib, ← Real.exp_sum]
  congr 2
  simp [tensorEnergy, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem tensor_overlap_integrable (m : (i : ι) → Measure (Ω i))
    [∀ i, SigmaFinite (m i)] (X Y : (i : ι) → Ω i → ℝ)
    (hI : ∀ i, Integrable (fun x => Real.exp (-(X i x + Y i x))) (m i)) :
    Integrable (fun x => Real.exp (-(tensorEnergy X x + tensorEnergy Y x))) (Measure.pi m) := by
  convert Integrable.fintype_prod_dep hI using 1
  funext x
  rw [← Real.exp_sum]
  simp [tensorEnergy, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem tensor_overlap_integral (m : (i : ι) → Measure (Ω i))
    [∀ i, SigmaFinite (m i)] (X Y : (i : ι) → Ω i → ℝ) :
    (∫ x, Real.exp (-(tensorEnergy X x + tensorEnergy Y x)) ∂Measure.pi m) =
      ∏ i, ∫ x, Real.exp (-(X i x + Y i x)) ∂m i := by
  convert integral_fintype_prod_eq_prod (μ := m)
    (fun i x => Real.exp (-(X i x + Y i x))) using 1
  congr 1
  funext x
  rw [← Real.exp_sum]
  simp [tensorEnergy, Finset.sum_add_distrib, Finset.sum_neg_distrib]

end ProductDensity

section ProductMoments

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}
  [∀ i, MeasurableSpace (Ω i)]

theorem tensorEnergy_memLp (μ : (i : ι) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (X : (i : ι) → Ω i → ℝ)
    (hX : ∀ i, MemLp (X i) 2 (μ i)) :
    MemLp (tensorEnergy X) 2 (Measure.pi μ) := by
  exact memLp_finsetSum _ (fun i _ => (hX i).comp_measurePreserving (measurePreserving_eval μ i))

theorem tensorEnergy_integral (μ : (i : ι) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (X : (i : ι) → Ω i → ℝ)
    (hX : ∀ i, Integrable (X i) (μ i)) :
    (∫ x, tensorEnergy X x ∂Measure.pi μ) = ∑ i, ∫ x, X i x ∂μ i := by
  change (∫ x, (∑ i, X i (x i)) ∂Measure.pi μ) = _
  rw [integral_finsetSum _ (fun i _ => integrable_comp_eval (hX i))]
  exact Finset.sum_congr rfl (fun i _ => integral_comp_eval (hX i).aestronglyMeasurable)

theorem tensorEnergy_variance (μ : (i : ι) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (X : (i : ι) → Ω i → ℝ)
    (hX : ∀ i, MemLp (X i) 2 (μ i)) :
    variance (tensorEnergy X) (Measure.pi μ) = ∑ i, variance (X i) (μ i) := by
  have heq : tensorEnergy X = ∑ i, fun x => X i (x i) := by
    funext x
    simp [tensorEnergy]
  rw [heq]
  exact variance_sum_pi hX

/-- The product overlap law has the summed endpoint means and a variance
bound linear in the number of blocks, derived from the individual laws. -/
theorem tensor_overlap_moments (m : (i : ι) → Measure (Ω i)) [∀ i, SigmaFinite (m i)]
    (X Y : (i : ι) → Ω i → ℝ) (Z mean : ι → ℝ) (C : ℝ)
    (hZ : ∀ i, 0 < Z i)
    (hI : ∀ i, Integrable (fun x => Real.exp (-(X i x + Y i x))) (m i))
    (hnorm : ∀ i, ∫ x, Real.exp (-(X i x + Y i x)) ∂m i = Z i)
    (hX : ∀ i, MemLp (X i) 2 (overlapLaw (m i) (X i) (Y i) (Z i)))
    (hY : ∀ i, MemLp (Y i) 2 (overlapLaw (m i) (X i) (Y i) (Z i)))
    (hmeanX : ∀ i, ∫ x, X i x ∂overlapLaw (m i) (X i) (Y i) (Z i) = mean i)
    (hmeanY : ∀ i, ∫ x, Y i x ∂overlapLaw (m i) (X i) (Y i) (Z i) = mean i)
    (hvX : ∀ i, variance (X i) (overlapLaw (m i) (X i) (Y i) (Z i)) ≤ C)
    (hvY : ∀ i, variance (Y i) (overlapLaw (m i) (X i) (Y i) (Z i)) ≤ C) :
    let μ := overlapLaw (Measure.pi m) (tensorEnergy X) (tensorEnergy Y) (∏ i, Z i)
    MemLp (tensorEnergy X) 2 μ ∧ MemLp (tensorEnergy Y) 2 μ ∧
      (∫ x, tensorEnergy X x ∂μ) = ∑ i, mean i ∧
      (∫ x, tensorEnergy Y x ∂μ) = ∑ i, mean i ∧
      variance (tensorEnergy X) μ ≤ Fintype.card ι * C ∧
      variance (tensorEnergy Y) μ ≤ Fintype.card ι * C := by
  let μ := fun i => overlapLaw (m i) (X i) (Y i) (Z i)
  letI (i : ι) : IsProbabilityMeasure (μ i) := overlapLaw_probability (m i) (X i) (Y i)
    (hZ i) (hI i) (hnorm i)
  dsimp only
  rw [tensor_overlapLaw m X Y Z hZ hI]
  refine ⟨tensorEnergy_memLp μ X hX, tensorEnergy_memLp μ Y hY, ?_, ?_, ?_, ?_⟩
  · rw [tensorEnergy_integral μ X (fun i => (hX i).integrable (by norm_num))]
    exact Finset.sum_congr rfl (fun i _ => hmeanX i)
  · rw [tensorEnergy_integral μ Y (fun i => (hY i).integrable (by norm_num))]
    exact Finset.sum_congr rfl (fun i _ => hmeanY i)
  · rw [tensorEnergy_variance μ X hX]
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hvX i)
  · rw [tensorEnergy_variance μ Y hY]
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hvY i)

end ProductMoments

end UnitDistance
