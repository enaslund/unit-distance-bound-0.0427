module

public import UnitDistance.Concentration
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section
set_option backward.privateInPublic true


/-!
# Removing the overlap density on the common energy window

`X` and `Y` are the two endpoint energies on the overlap space. Its ordinary
measure includes positions and displacements; the probability density is
`exp (-(X + Y)) / Z`. Zero-profile points are omitted from that space.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UnitDistance

noncomputable def overlapLaw {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) (Z : ℝ) : Measure Ω :=
  m.withDensity (fun ω => ENNReal.ofReal (Real.exp (-(X ω + Y ω)) / Z))

theorem overlapLaw_real {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) {Z : ℝ} (hZ : 0 < Z)
    (hI : Integrable (fun ω => Real.exp (-(X ω + Y ω))) m)
    {s : Set Ω} (hs : MeasurableSet s) :
    (overlapLaw m X Y Z).real s =
      ∫ ω in s, Real.exp (-(X ω + Y ω)) / Z ∂m := by
  rw [measureReal_def, overlapLaw, withDensity_apply _ hs,
    ← integral_eq_lintegral_of_nonneg_ae]
  · exact Filter.Eventually.of_forall (fun _ => div_nonneg (Real.exp_pos _).le hZ.le)
  · exact (hI.div_const Z).integrableOn.aestronglyMeasurable

theorem overlapLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) {Z : ℝ} (hZ : 0 < Z)
    (hI : Integrable (fun ω => Real.exp (-(X ω + Y ω))) m)
    (hnorm : ∫ ω, Real.exp (-(X ω + Y ω)) ∂m = Z) :
    IsProbabilityMeasure (overlapLaw m X Y Z) := by
  constructor
  rw [overlapLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hI.div_const Z)
      (Filter.Eventually.of_forall (fun _ => div_nonneg (Real.exp_pos _).le hZ.le)),
    integral_div, hnorm, div_self hZ.ne', ENNReal.ofReal_one]

/-- Undoing the overlap density costs exactly the two lower endpoint energies.
The event `G` may be the simultaneous concentration event, and `W` the event
that both endpoints lie in the common sublevel window. -/
theorem overlap_unweight {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) {Z q lower : ℝ}
    (hZ : 0 < Z) (hI : Integrable (fun ω => Real.exp (-(X ω + Y ω))) m)
    {G W : Set Ω} (hG : MeasurableSet G) (hGW : G ⊆ W) (hWfin : m W ≠ ∞)
    (hX : ∀ ω ∈ G, lower ≤ X ω) (hY : ∀ ω ∈ G, lower ≤ Y ω)
    (hmass : q ≤ (overlapLaw m X Y Z).real G) :
    q * Z * Real.exp (2 * lower) ≤ m.real W := by
  have hGfin : m G ≠ ∞ := measure_ne_top_of_subset hGW hWfin
  have hdom : ∀ ω ∈ G, Real.exp (-(X ω + Y ω)) / Z ≤
      Real.exp (-(2*lower)) / Z := by
    intro ω hω
    apply div_le_div_of_nonneg_right _ hZ.le
    apply Real.exp_le_exp.mpr
    linarith [hX ω hω, hY ω hω]
  have hbound := setIntegral_mono_on (hI.div_const Z).integrableOn
    (integrableOn_const hGfin) hG hdom
  simp only [integral_const, smul_eq_mul, measureReal_def,
    Measure.restrict_apply_univ] at hbound
  have hvol := measureReal_mono hGW hWfin
  have hc : 0 < Real.exp (-(2*lower)) / Z := div_pos (Real.exp_pos _) hZ
  have hv : q ≤ Real.exp (-(2*lower)) / Z * m.real W := by
    calc
      q ≤ (overlapLaw m X Y Z).real G := hmass
      _ = ∫ ω in G, Real.exp (-(X ω + Y ω)) / Z ∂m := overlapLaw_real m X Y hZ hI hG
      _ ≤ m.real G * (Real.exp (-(2*lower)) / Z) := hbound
      _ ≤ Real.exp (-(2*lower)) / Z * m.real W := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hvol hc.le
  have hmul := mul_le_mul_of_nonneg_right hv (mul_pos hZ (Real.exp_pos (2*lower))).le
  have he : Real.exp (-(2*lower)) * Real.exp (2*lower) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    q * Z * Real.exp (2*lower) = q * (Z * Real.exp (2*lower)) := by ring
    _ ≤ (Real.exp (-(2*lower)) / Z * m.real W) * (Z * Real.exp (2*lower)) := hmul
    _ = m.real W := by
      field_simp
      linear_combination m.real W * he

/-- Chebyshev, a union bound, and removal of the *same* overlap density yield
the exact lower overlap of the common upper energy window. -/
theorem common_energy_window_overlap {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) {Z C ε d mean : ℝ}
    (hZ : 0 < Z) (hI : Integrable (fun ω => Real.exp (-(X ω + Y ω))) m)
    (hnorm : ∫ ω, Real.exp (-(X ω + Y ω)) ∂m = Z)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX : MemLp X 2 (overlapLaw m X Y Z))
    (hY : MemLp Y 2 (overlapLaw m X Y Z))
    (hmeanX : ∫ ω, X ω ∂overlapLaw m X Y Z = mean)
    (hmeanY : ∫ ω, Y ω ∂overlapLaw m X Y Z = mean)
    (hε : 0 < ε) (hd : 0 < d)
    (hvX : variance X (overlapLaw m X Y Z) ≤ C*d)
    (hvY : variance Y (overlapLaw m X Y Z) ≤ C*d)
    (hlarge : 4*C ≤ ε^2*d)
    (hWfin : m {ω | X ω ≤ mean + ε*d ∧ Y ω ≤ mean + ε*d} ≠ ∞) :
    (1/2 : ℝ) * Z * Real.exp (2*(mean - ε*d)) ≤
      m.real {ω | X ω ≤ mean + ε*d ∧ Y ω ≤ mean + ε*d} := by
  let μ := overlapLaw m X Y Z
  letI : IsProbabilityMeasure μ := overlapLaw_probability m X Y hZ hI hnorm
  have hm := two_endpoint_half_mass μ X Y hXm hYm hX hY C ε d hε hd hvX hvY hlarge
  rw [hmeanX, hmeanY] at hm
  let G := {ω | |X ω - mean| < ε*d ∧ |Y ω - mean| < ε*d}
  have hMX : Measurable (fun ω => |X ω - mean|) := by
    simpa only [Real.norm_eq_abs] using (hXm.sub_const mean).norm
  have hMY : Measurable (fun ω => |Y ω - mean|) := by
    simpa only [Real.norm_eq_abs] using (hYm.sub_const mean).norm
  have hG : MeasurableSet G := by
    change MeasurableSet ({ω | |X ω - mean| < ε*d} ∩ {ω | |Y ω - mean| < ε*d})
    exact (measurableSet_lt hMX measurable_const).inter (measurableSet_lt hMY measurable_const)
  apply overlap_unweight m X Y hZ hI hG (W := {ω | X ω ≤ mean + ε*d ∧ Y ω ≤ mean + ε*d})
    (lower := mean - ε*d) (q := 1/2) ?_ hWfin ?_ ?_ hm
  · intro ω hω
    obtain ⟨hx, hy⟩ := hω
    have hx' := (abs_lt.mp hx).2
    have hy' := (abs_lt.mp hy).2
    constructor <;> linarith
  · intro ω hω
    have h := (abs_lt.mp hω.1).1
    linarith
  · intro ω hω
    have h := (abs_lt.mp hω.2).1
    linarith

/-- Exponential majorization of the volume of a sublevel energy window. -/
theorem energy_window_volume {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (E : Ω → ℝ) (p T : ℝ) (hp : 0 ≤ p)
    (hEm : Measurable E) (hI : Integrable (fun x => Real.exp (-p*E x)) m)
    (hfin : m {x | E x ≤ T} ≠ ∞) :
    m.real {x | E x ≤ T} ≤ Real.exp (p*T) * ∫ x, Real.exp (-p*E x) ∂m := by
  have hs : MeasurableSet {x | E x ≤ T} := measurableSet_le hEm measurable_const
  have hle := setIntegral_mono_on (integrableOn_const hfin) hI.integrableOn hs
    (show ∀ x ∈ {x | E x ≤ T}, Real.exp (-p*T) ≤ Real.exp (-p*E x) by
      intro x hx
      apply Real.exp_le_exp.mpr
      change E x ≤ T at hx
      nlinarith)
  simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] at hle
  have hwhole : (∫ x in {x | E x ≤ T}, Real.exp (-p*E x) ∂m) ≤
      ∫ x, Real.exp (-p*E x) ∂m :=
    setIntegral_le_integral hI (Filter.Eventually.of_forall
      (fun x => (Real.exp_pos (-p*E x)).le))
  have he : Real.exp (-p*T) * Real.exp (p*T) = 1 := by
    rw [← Real.exp_add]
    rw [show -p*T + p*T = 0 by ring, Real.exp_zero]
  have h := mul_le_mul_of_nonneg_right (hle.trans hwhole) (Real.exp_pos (p*T)).le
  nlinarith [show m.real {x | E x ≤ T} * Real.exp (-p*T) * Real.exp (p*T) =
    m.real {x | E x ≤ T} by linear_combination m.real {x | E x ≤ T} * he]

/-- The identical exponential majorant applies pointwise to any finite set
inside the window, allowing a uniform weighted lattice bound to be used. -/
theorem energy_window_card {Ω : Type*} (V : Finset Ω) (E : Ω → ℝ)
    (p T : ℝ) (hp : 0 ≤ p) (hV : ∀ x ∈ V, E x ≤ T) :
    (V.card : ℝ) ≤ Real.exp (p*T) * ∑ x ∈ V, Real.exp (-p*E x) := by
  have h : ∑ _x ∈ V, (1 : ℝ) ≤ ∑ x ∈ V, Real.exp (p*T) * Real.exp (-p*E x) := by
    apply Finset.sum_le_sum
    intro x hx
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [hV x hx]
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum] using h

end UnitDistance
