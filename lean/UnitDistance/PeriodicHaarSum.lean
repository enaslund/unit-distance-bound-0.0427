module

public import UnitDistance.ProductMeasurableGroup
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
set_option backward.privateInPublic true


/-!
# Finite sums of a periodic local profile

Distinct cosets of an actual measurable additive period have disjoint Haar
mass. A finite sum of their profile values is bounded by the full profile
integral divided by the period volume. This is the finite-place factor in
the S-integer weighted lattice bound.
-/

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators
namespace UnitDistance

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
  (μ : Measure G) [μ.IsAddRightInvariant]

theorem periodic_finite_coset_sum_mul_measure_le
    (P : AddSubgroup G) (hP : MeasurableSet (P : Set G))
    (g : G → ℝ≥0∞) (hg : ∀ p ∈ P, ∀ x, g (x+p) = g x)
    {J : Type*} (s : Finset J) (r : J → G)
    (hr : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → r i-r j ∉ P) :
    (∑ i ∈ s, g (r i)) * μ P ≤ ∫⁻ x, g x ∂μ := by
  let C (i : J) : Set G := {x | x-r i ∈ P}
  have hCm (i : J) : MeasurableSet (C i) := by
    simpa [C, sub_eq_add_neg, Set.preimage] using hP.preimage (measurable_id.add_const (-r i))
  have hCvol (i : J) : μ (C i) = μ P := by
    change μ ((fun x => x-r i) ⁻¹' (P : Set G)) = μ P
    simp only [sub_eq_add_neg, measure_preimage_add_right]
  have heq (i : J) {x : G} (hx : x ∈ C i) : g x = g (r i) := by
    have h := hg (x-r i) hx (r i)
    rwa [show r i+(x-r i) = x by abel] at h
  have hdisj (i : J) (hi : i ∈ s) (j : J) (hj : j ∈ s) (hij : i ≠ j) :
      Disjoint (C i) (C j) := by
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    apply hr i hi j hj hij
    convert P.sub_mem hxj hxi using 1
    abel
  have hpoint (x : G) : (∑ i ∈ s, (C i).indicator (fun _ => g (r i)) x) ≤ g x := by
    by_cases hx : ∃ i ∈ s, x ∈ C i
    · obtain ⟨i, hi, hxi⟩ := hx
      rw [Finset.sum_eq_single i]
      · rw [Set.indicator_of_mem hxi, heq i hxi]
      · intro j hj hji
        apply Set.indicator_of_notMem
        intro hxj
        exact Set.disjoint_left.mp (hdisj j hj i hi hji) hxj hxi
      · exact fun h => False.elim (h hi)
    · have hz : ∀ i ∈ s, (C i).indicator (fun _ => g (r i)) x = 0 := by
        intro i hi
        exact Set.indicator_of_notMem (fun hxi => hx ⟨i, hi, hxi⟩) _
      simp only [Finset.sum_congr rfl hz, Finset.sum_const_zero, zero_le]
  calc
    (∑ i ∈ s, g (r i)) * μ P =
        ∑ i ∈ s, ∫⁻ x, (C i).indicator (fun _ => g (r i)) x ∂μ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by rw [lintegral_indicator_const (hCm i), hCvol])
    _ = ∫⁻ x, ∑ i ∈ s, (C i).indicator (fun _ => g (r i)) x ∂μ := by
      rw [lintegral_finsetSum s (fun i _ => measurable_const.indicator (hCm i))]
    _ ≤ ∫⁻ x, g x ∂μ := lintegral_mono hpoint

/-- Real-valued form for an actual nonnegative integrable local profile. -/
theorem periodic_finite_coset_sum_mul_measureReal_le
    (P : AddSubgroup G) (hP : MeasurableSet (P : Set G))
    (g : G → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g μ)
    (hg : ∀ p ∈ P, ∀ x, g (x+p) = g x)
    {J : Type*} (s : Finset J) (r : J → G)
    (hr : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → r i-r j ∉ P) :
    (∑ i ∈ s, g (r i)) * μ.real P ≤ ∫ x, g x ∂μ := by
  have hh := periodic_finite_coset_sum_mul_measure_le μ P hP
    (fun x => ENNReal.ofReal (g x)) (fun p hp x => congrArg ENNReal.ofReal (hg p hp x)) s r hr
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)] at hh
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (hg0 _), ENNReal.toReal_ofReal (integral_nonneg hg0),
    measureReal_def] using h

end UnitDistance
