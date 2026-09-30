module

public import UnitDistance.GeometryTiling
public import UnitDistance.GeometryLogSupport
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Compact logarithmic support of actual reciprocal overlaps

Boundedness of both coordinates in each complex pair forces the logarithmic
displacement into a fixed compact box. This proves the support hypothesis
needed for uniform finite unit-lattice truncation, for actual overlap measures.
-/

open MeasureTheory
open scoped ENNReal

namespace UnitDistance

theorem projected_step_norm_le {X : Type*} [AddCommGroup X]
    (φ : X →+ ℂ) (Ω : Set X) {R : ℝ}
    (hΩ : ∀ x ∈ Ω, ‖φ x‖ ≤ R) {x β : X}
    (hx : x ∈ Ω) (hy : x + β ∈ Ω) : ‖φ β‖ ≤ 2*R := by
  calc
    ‖φ β‖ = ‖φ (x + β) - φ x‖ := by rw [map_add, add_sub_cancel_left]
    _ ≤ ‖φ (x+β)‖ + ‖φ x‖ := norm_sub_le _ _
    _ ≤ 2*R := by linarith [hΩ x hx, hΩ (x+β) hy]

/-- The actual overlap-volume profile vanishes outside a compact logarithmic
box whenever each displacement has reciprocal complex-coordinate moduli. -/
theorem reciprocal_overlap_compactSupport {X ι : Type*} [AddCommGroup X]
    [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (Ω : Set X) (plus minus : ι → X →+ ℂ)
    (step : (ι → ℝ) → X) {R : ℝ} (hR : 0 < R)
    (hplus : ∀ x ∈ Ω, ∀ i, ‖plus i x‖ ≤ R)
    (hminus : ∀ x ∈ Ω, ∀ i, ‖minus i x‖ ≤ R)
    (hstepPlus : ∀ u i, ‖plus i (step u)‖ = Real.exp (u i))
    (hstepMinus : ∀ u i, ‖minus i (step u)‖ = Real.exp (-u i)) :
    HasCompactSupport (fun u => μ (overlapSet Ω (step u))) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (fun _ : ι => -Real.log (2*R))
      (fun _ : ι => Real.log (2*R))))
  intro u hu
  have hne : (overlapSet Ω (step u)).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    have hz : μ (overlapSet Ω (step u)) = 0 := by rw [he]; exact measure_empty
    exact hu hz
  obtain ⟨x, hx, hy⟩ := hne
  have hP (i : ι) : u i ≤ Real.log (2*R) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    rw [← hstepPlus]
    exact projected_step_norm_le (plus i) Ω (fun x hx => hplus x hx i) hx hy
  have hM (i : ι) : -Real.log (2*R) ≤ u i := by
    have h := projected_step_norm_le (minus i) Ω (fun x hx => hminus x hx i) hx hy
    rw [hstepMinus] at h
    have := (Real.le_log_iff_exp_le (by positivity)).mpr h
    linarith
  exact ⟨hM, hP⟩

end UnitDistance
