module

public import UnitDistance.EnergyWindow
public import UnitDistance.GeometryTiling

@[expose] public section
set_option backward.privateInPublic true


/-!
# Concentration yields the overlap of an actual position window

The endpoint space here is explicitly displacement × position. Thus the
energy event in the concentration theorem is the ordinary overlap of the
same sublevel set at its two endpoints, not an unrelated probability event.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UnitDistance

def energyWindow {X : Type*} (E : X → ℝ) (T : ℝ) : Set X := {x | E x ≤ T}

def firstEnergy {D X : Type*} (E : X → ℝ) (z : D × X) : ℝ := E z.2

def secondEnergy {D X : Type*} [Add X] (E : X → ℝ) (step : D → X)
    (z : D × X) : ℝ := E (z.2 + step z.1)

noncomputable def windowOverlap {D X : Type*} [AddCommGroup X]
    [MeasurableSpace D] [MeasurableSpace X]
    (σ : Measure D) (μ : Measure X) (step : D → X) (E : X → ℝ) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ β, μ (overlapSet (energyWindow E T) (step β)) ∂σ

theorem windowOverlap_eq_pair_measure {D X : Type*}
    [MeasurableSpace D] [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]
    (σ : Measure D) (μ : Measure X) [SFinite μ]
    (step : D → X) (hstep : Measurable step) (E : X → ℝ) (hE : Measurable E) (T : ℝ) :
    windowOverlap σ μ step E T =
      (σ.prod μ) {z | firstEnergy E z ≤ T ∧ secondEnergy E step z ≤ T} := by
  have hfirst : Measurable (firstEnergy (D := D) E) := hE.comp measurable_snd
  have hsecond : Measurable (secondEnergy E step) :=
    hE.comp (measurable_snd.add (hstep.comp measurable_fst))
  have hs : MeasurableSet {z : D × X | firstEnergy E z ≤ T ∧ secondEnergy E step z ≤ T} :=
    (measurableSet_le hfirst (show Measurable (fun _ : D × X => T) from measurable_const)).inter
      (measurableSet_le hsecond (show Measurable (fun _ : D × X => T) from measurable_const))
  rw [Measure.prod_apply hs]
  rfl

/-- The concentrated overlap is the integral of actual translated-window
intersection measures over the original displacement measure. -/
theorem concentrated_windowOverlap {D X : Type*}
    [MeasurableSpace D] [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]
    (σ : Measure D) (μ : Measure X) [SFinite μ]
    (step : D → X) (hstep : Measurable step) (E : X → ℝ) (hE : Measurable E)
    {Z C ε d mean : ℝ} (hZ : 0 < Z)
    (hI : Integrable (fun z : D × X =>
      Real.exp (-(firstEnergy E z + secondEnergy E step z))) (σ.prod μ))
    (hnorm : (∫ z : D × X, Real.exp (-(firstEnergy E z + secondEnergy E step z))
      ∂σ.prod μ) = Z)
    (hX : MemLp (firstEnergy E) 2
      (overlapLaw (σ.prod μ) (firstEnergy E) (secondEnergy E step) Z))
    (hY : MemLp (secondEnergy E step) 2
      (overlapLaw (σ.prod μ) (firstEnergy E) (secondEnergy E step) Z))
    (hmeanX : (∫ z, firstEnergy E z
      ∂overlapLaw (σ.prod μ) (firstEnergy E) (secondEnergy E step) Z) = mean)
    (hmeanY : (∫ z, secondEnergy E step z
      ∂overlapLaw (σ.prod μ) (firstEnergy E) (secondEnergy E step) Z) = mean)
    (hε : 0 < ε) (hd : 0 < d)
    (hvX : variance (firstEnergy E)
      (overlapLaw (σ.prod μ) (firstEnergy E) (secondEnergy E step) Z) ≤ C*d)
    (hvY : variance (secondEnergy E step)
      (overlapLaw (σ.prod μ) (firstEnergy E) (secondEnergy E step) Z) ≤ C*d)
    (hlarge : 4*C ≤ ε^2*d)
    (hfin : windowOverlap σ μ step E (mean+ε*d) ≠ ∞) :
    (1/2 : ℝ)*Z*Real.exp (2*(mean-ε*d)) ≤
      (windowOverlap σ μ step E (mean+ε*d)).toReal := by
  rw [windowOverlap_eq_pair_measure σ μ step hstep E hE] at hfin ⊢
  exact common_energy_window_overlap (σ.prod μ) (firstEnergy E) (secondEnergy E step)
    hZ hI hnorm (hE.comp measurable_snd)
    (hE.comp (measurable_snd.add (hstep.comp measurable_fst)))
    hX hY hmeanX hmeanY hε hd hvX hvY hlarge hfin

end UnitDistance
