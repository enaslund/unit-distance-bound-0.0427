module

public import UnitDistance.ProfileOverlap

@[expose] public section
set_option backward.privateInPublic true


/-!
# Energy windows for profiles with zeros

The profile equals `exp (-E)` on its measurable support `S` and is zero
elsewhere. Energies outside `S` have no effect. The overlap probability uses
the restriction of displacement × Haar measure to pairs in `S`; Haar measure
itself is not restricted when geometric window volumes are computed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UnitDistance

def supportedWindow {X : Type*} (S : Set X) (E : X → ℝ) (T : ℝ) : Set X :=
  S ∩ energyWindow E T

noncomputable def supportedOverlapMeasure {D X : Type*} [Add X]
    [MeasurableSpace D] [MeasurableSpace X]
    (σ : Measure D) (μ : Measure X) (step : D → X) (S : Set X) : Measure (D × X) :=
  (σ.prod μ).restrict {z | z.2 ∈ S ∧ z.2 + step z.1 ∈ S}

noncomputable def supportedWindowOverlap {D X : Type*} [AddCommGroup X]
    [MeasurableSpace D] [MeasurableSpace X]
    (σ : Measure D) (μ : Measure X) (step : D → X)
    (S : Set X) (E : X → ℝ) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ β, μ (overlapSet (supportedWindow S E T) (step β)) ∂σ

theorem measurableSet_supportedWindow {X : Type*} [MeasurableSpace X]
    {S : Set X} (hS : MeasurableSet S) {E : X → ℝ} (hE : Measurable E) (T : ℝ) :
    MeasurableSet (supportedWindow S E T) :=
  hS.inter (measurableSet_le hE measurable_const)

theorem supportedWindowOverlap_eq_pair_measure {D X : Type*}
    [MeasurableSpace D] [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]
    (σ : Measure D) (μ : Measure X) [SFinite μ]
    (step : D → X) (hstep : Measurable step)
    (S : Set X) (hS : MeasurableSet S) (E : X → ℝ) (hE : Measurable E) (T : ℝ) :
    supportedWindowOverlap σ μ step S E T =
      supportedOverlapMeasure σ μ step S
        {z | firstEnergy E z ≤ T ∧ secondEnergy E step z ≤ T} := by
  have hfirst : Measurable (firstEnergy (D := D) E) := hE.comp measurable_snd
  have hsecond : Measurable (secondEnergy E step) :=
    hE.comp (measurable_snd.add (hstep.comp measurable_fst))
  have hs : MeasurableSet {z : D × X | firstEnergy E z ≤ T ∧ secondEnergy E step z ≤ T} :=
    (measurableSet_le hfirst (show Measurable (fun _ : D × X => T) from measurable_const)).inter
      (measurableSet_le hsecond (show Measurable (fun _ : D × X => T) from measurable_const))
  have hW := measurableSet_supportedWindow hS hE T
  have hpair : MeasurableSet {z : D × X |
      z.2 ∈ supportedWindow S E T ∧ z.2 + step z.1 ∈ supportedWindow S E T} :=
    (hW.preimage measurable_snd).inter
      (hW.preimage (measurable_snd.add (hstep.comp measurable_fst)))
  rw [supportedOverlapMeasure, Measure.restrict_apply hs]
  have heq : {z : D × X | firstEnergy E z ≤ T ∧ secondEnergy E step z ≤ T} ∩
      {z | z.2 ∈ S ∧ z.2 + step z.1 ∈ S} =
      {z | z.2 ∈ supportedWindow S E T ∧ z.2 + step z.1 ∈ supportedWindow S E T} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, supportedWindow, energyWindow,
      firstEnergy, secondEnergy]
    tauto
  rw [heq, Measure.prod_apply hpair]
  rfl

/-- Two endpoint concentration for an actual window inside the support of a
possibly vanishing profile. No positivity is required outside the support. -/
theorem concentrated_supportedWindowOverlap {D X : Type*}
    [MeasurableSpace D] [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]
    (σ : Measure D) (μ : Measure X) [SFinite μ]
    (step : D → X) (hstep : Measurable step)
    (S : Set X) (hS : MeasurableSet S) (E : X → ℝ) (hE : Measurable E)
    {Z C ε d mean : ℝ} (hZ : 0 < Z)
    (hI : Integrable (fun z : D × X =>
      Real.exp (-(firstEnergy E z + secondEnergy E step z)))
      (supportedOverlapMeasure σ μ step S))
    (hnorm : (∫ z : D × X, Real.exp (-(firstEnergy E z + secondEnergy E step z))
      ∂supportedOverlapMeasure σ μ step S) = Z)
    (hX : MemLp (firstEnergy E) 2
      (overlapLaw (supportedOverlapMeasure σ μ step S)
        (firstEnergy E) (secondEnergy E step) Z))
    (hY : MemLp (secondEnergy E step) 2
      (overlapLaw (supportedOverlapMeasure σ μ step S)
        (firstEnergy E) (secondEnergy E step) Z))
    (hmeanX : (∫ z, firstEnergy E z
      ∂overlapLaw (supportedOverlapMeasure σ μ step S)
        (firstEnergy E) (secondEnergy E step) Z) = mean)
    (hmeanY : (∫ z, secondEnergy E step z
      ∂overlapLaw (supportedOverlapMeasure σ μ step S)
        (firstEnergy E) (secondEnergy E step) Z) = mean)
    (hε : 0 < ε) (hd : 0 < d)
    (hvX : variance (firstEnergy E)
      (overlapLaw (supportedOverlapMeasure σ μ step S)
        (firstEnergy E) (secondEnergy E step) Z) ≤ C*d)
    (hvY : variance (secondEnergy E step)
      (overlapLaw (supportedOverlapMeasure σ μ step S)
        (firstEnergy E) (secondEnergy E step) Z) ≤ C*d)
    (hlarge : 4*C ≤ ε^2*d)
    (hfin : supportedWindowOverlap σ μ step S E (mean+ε*d) ≠ ∞) :
    (1/2 : ℝ)*Z*Real.exp (2*(mean-ε*d)) ≤
      (supportedWindowOverlap σ μ step S E (mean+ε*d)).toReal := by
  rw [supportedWindowOverlap_eq_pair_measure σ μ step hstep S hS E hE] at hfin ⊢
  exact common_energy_window_overlap (supportedOverlapMeasure σ μ step S)
    (firstEnergy E) (secondEnergy E step) hZ hI hnorm
    (hE.comp measurable_snd) (hE.comp (measurable_snd.add (hstep.comp measurable_fst)))
    hX hY hmeanX hmeanY hε hd hvX hvY hlarge hfin

theorem supported_energy_window_volume {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (E : X → ℝ) (p T : ℝ) (hp : 0 ≤ p)
    (hE : Measurable E)
    (hI : Integrable (fun x => Real.exp (-p*E x)) (μ.restrict S))
    (hfin : μ (supportedWindow S E T) ≠ ∞) :
    μ.real (supportedWindow S E T) ≤
      Real.exp (p*T) * ∫ x in S, Real.exp (-p*E x) ∂μ := by
  have hs : MeasurableSet {x | E x ≤ T} := measurableSet_le hE measurable_const
  have heq : (μ.restrict S) {x | E x ≤ T} = μ (supportedWindow S E T) := by
    rw [Measure.restrict_apply hs]
    congr 1
    exact Set.inter_comm _ _
  have h := energy_window_volume (μ.restrict S) E p T hp hE hI (heq ▸ hfin)
  simpa only [measureReal_def, heq] using h

end UnitDistance
