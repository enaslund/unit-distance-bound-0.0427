module

public import UnitDistance.GeometryAveraging
public import UnitDistance.GeometryTiling
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option backward.privateInPublic true


/-!
# Conditional geometric transfer from actual windows

The averaging identities in this file are *proved* from additive tiling.
Input configurations are required to enumerate exactly the lattice points
in the stated windows. Thus the analytic inputs concern actual window
volumes, actual overlap volumes and a uniform point bound, rather than a
hypothesis already asserting the desired graph ratio.
-/

open scoped Classical BigOperators ENNReal
open MeasureTheory

namespace UnitDistance

section FixedLattice

variable {X : Type*} [AddCommGroup X] [MeasurableSpace X]
  [MeasurableAdd₂ X]
  (L : AddSubgroup X) [Countable L]
  (μ : Measure X)
  [VAddInvariantMeasure L X μ]
  (P : Set X) (hP : IsAddFundamentalDomain L P μ)
  (Ω : Set X) (hΩ : MeasurableSet Ω)
  (V : X → Finset L) (hV : ∀ h l, l ∈ V h ↔ (l : X) + h ∈ Ω)

include hV hP hΩ in
/-- The real vertex-count integral follows from the nonnegative tiling
identity; finite window volume supplies all needed integrability. -/
theorem lattice_vertex_integral (hvol : μ Ω ≠ ⊤) :
    Integrable (fun h => ((V h).card : ℝ)) (μ.restrict P) ∧
    (∫ h in P, ((V h).card : ℝ) ∂μ) = (μ Ω).toReal := by
  have hm : Measurable (translatedLatticeCount L Ω) :=
    Measurable.tsum (fun l => (measurable_const.indicator hΩ).comp
      (measurable_const.add measurable_id))
  have heq (h : X) : translatedLatticeCount L Ω h = ((V h).card : ℝ≥0∞) :=
    lattice_count_eq_card L Ω h (V h) (hV h)
  have htop : ∀ h, translatedLatticeCount L Ω h ≠ ⊤ := by intro h; rw [heq]; simp
  have hint : Integrable (fun h => (translatedLatticeCount L Ω h).toReal) (μ.restrict P) :=
    (integrable_toReal_iff hm.aemeasurable (Filter.Eventually.of_forall htop)).mpr
      (by rw [lattice_vertex_average L μ P hP Ω hΩ]; exact hvol)
  have hval := integral_toReal (μ := μ.restrict P) hm.aemeasurable
    (Filter.Eventually.of_forall (fun h => (htop h).lt_top))
  rw [lattice_vertex_average L μ P hP Ω hΩ] at hval
  simp_rw [heq, ENNReal.toReal_natCast] at hint hval
  exact ⟨hint, hval⟩

include hV hP hΩ in
/-- The exact real ordered-edge integral, including the finite-displacement
cardinality calculation. -/
theorem lattice_edge_integral (D : Finset L) (hvol : μ Ω ≠ ⊤) :
    Integrable (fun h => ((displacementPairs (V h) D).card : ℝ)) (μ.restrict P) ∧
    (∫ h in P, ((displacementPairs (V h) D).card : ℝ) ∂μ) =
      ∑ β ∈ D, (μ (overlapSet Ω (β : X))).toReal := by
  have hm : Measurable (translatedLatticeEdgeCount L Ω D) :=
    Finset.measurable_sum _ (fun β _ => Measurable.tsum (fun l =>
      (measurable_const.indicator (measurable_overlapSet Ω hΩ β)).comp
        (measurable_const.add measurable_id)))
  have heq (h : X) : translatedLatticeEdgeCount L Ω D h =
      ((displacementPairs (V h) D).card : ℝ≥0∞) :=
    lattice_edge_count_eq_card L Ω h (V h) D (hV h)
  have htop : ∀ h, translatedLatticeEdgeCount L Ω D h ≠ ⊤ := by intro h; rw [heq]; simp
  have hOverlap (β : L) : μ (overlapSet Ω (β : X)) ≠ ⊤ :=
    ne_top_of_le_ne_top hvol (measure_mono Set.inter_subset_left)
  have hsum : (∑ β ∈ D, μ (overlapSet Ω (β : X))) ≠ ⊤ := by
    exact (ENNReal.sum_lt_top.mpr (fun β _ => (hOverlap β).lt_top)).ne
  have hint : Integrable (fun h => (translatedLatticeEdgeCount L Ω D h).toReal) (μ.restrict P) :=
    (integrable_toReal_iff hm.aemeasurable (Filter.Eventually.of_forall htop)).mpr
      (by rw [lattice_edge_average L μ P hP Ω hΩ]; exact hsum)
  have hval := integral_toReal (μ := μ.restrict P) hm.aemeasurable
    (Filter.Eventually.of_forall (fun h => (htop h).lt_top))
  rw [lattice_edge_average L μ P hP Ω hΩ, ENNReal.toReal_sum (fun β _ => hOverlap β)] at hval
  simp_rw [heq, ENNReal.toReal_natCast] at hint hval
  exact ⟨hint, hval⟩

include hV hP hΩ in
/-- A genuine finite planar set extracted from one favorable translate.
The input lower bound is about overlap volumes, with all graph averaging
and all edge/vertex normalization proved in the theorem. -/
theorem lattice_window_transfer (D : Finset L) (φ : L →+ ℂ)
    (hφ : Function.Injective φ) (hD : ∀ β ∈ D, ‖φ β‖ = 1)
    (a B δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hvol0 : μ Ω ≠ 0) (hvol : μ Ω ≠ ⊤)
    (hoverlap : a * (μ Ω).toReal ≤ ∑ β ∈ D, (μ (overlapSet Ω (β : X))).toReal)
    (hbound : ∀ h, ((V h).card : ℝ) ≤ B) :
    ∃ U : Finset ℂ, 0 < U.card ∧ (U.card : ℝ) ≤ B ∧
      a / (2 * B ^ δ) ≤ unitPairs U / (U.card : ℝ) ^ (1 + δ) := by
  obtain ⟨hNi, hNv⟩ := lattice_vertex_integral L μ P hP Ω hΩ V hV hvol
  obtain ⟨hEi, hEv⟩ := lattice_edge_integral L μ P hP Ω hΩ V hV D hvol
  obtain ⟨h, hn, hb, he⟩ := exists_joint_parameter_rpow (μ.restrict P)
    (fun h => ((V h).card : ℝ)) (fun h => ((displacementPairs (V h) D).card : ℝ))
    a B δ hNi hEi (fun _ => Nat.cast_nonneg _)
    (fun h hz => by
      have hv : V h = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hz)
      simp [hv])
    (by rw [hNv]; exact ENNReal.toReal_pos hvol0 hvol)
    (by rw [hNv, hEv]; exact hoverlap) ha hδ hbound
  obtain ⟨U, hcard, hu⟩ := project_displacement_graph (V h) D φ hφ (by
    intro x hx y hy hxy
    rw [dist_eq_norm, norm_sub_rev, ← map_sub]
    exact hD _ hxy)
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hcard]; exact_mod_cast hn
  · simpa only [hcard] using hb
  · rw [hcard]
    have hp : 0 < ((V h).card : ℝ) ^ (1 + δ) := Real.rpow_pos_of_pos hn _
    calc
      a / (2 * B ^ δ) = (a / B ^ δ) / 2 := by ring
      _ ≤ (((displacementPairs (V h) D).card : ℝ) / ((V h).card : ℝ) ^ (1 + δ)) / 2 :=
        div_le_div_of_nonneg_right he (by norm_num)
      _ = (((displacementPairs (V h) D).card : ℝ) / 2) / ((V h).card : ℝ) ^ (1 + δ) := by ring
      _ ≤ unitPairs U / ((V h).card : ℝ) ^ (1 + δ) := div_le_div_of_nonneg_right hu hp.le

end FixedLattice

section Families

variable {T X : Type*} [MeasurableSpace T]
  [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]
  (L : AddSubgroup X) [Countable L]

/-- Joint measurability follows from the measurable family of windows,
without a regularity assumption on its boundary. -/
theorem measurable_family_lattice_count (Ω : T → Set X)
    (hΩ : MeasurableSet {p : T × X | p.2 ∈ Ω p.1}) :
    Measurable (fun p : T × X => translatedLatticeCount L (Ω p.1) p.2) := by
  apply Measurable.tsum
  intro l
  exact (measurable_const.indicator hΩ).comp
    (measurable_fst.prodMk (measurable_const.add measurable_snd))

/-- Joint measurability for actual inherited ordered edges. -/
theorem measurable_family_lattice_edgeCount (Ω : T → Set X)
    (hΩ : MeasurableSet {p : T × X | p.2 ∈ Ω p.1}) (D : Finset L) :
    Measurable (fun p : T × X => translatedLatticeEdgeCount L (Ω p.1) D p.2) := by
  apply Finset.measurable_sum
  intro β hβ
  apply Measurable.tsum
  intro l
  have hm : MeasurableSet {p : T × X | p.2 ∈ Ω p.1 ∧ p.2 + (β : X) ∈ Ω p.1} :=
    hΩ.inter (hΩ.preimage (measurable_fst.prodMk (measurable_snd.add_const (β : X))))
  exact (measurable_const.indicator hm).comp
    (measurable_fst.prodMk (measurable_const.add measurable_snd))

/-- Joint selection over an arbitrary finite measure of reciprocal
parameters and all additive translations. Tiling and Fubini establish the
averages from actual window membership; the uniform bound applies at the
same pair of parameters returned by weighted averaging. -/
theorem family_window_transfer
    (ν : Measure T) [IsFiniteMeasure ν]
    (μ : Measure X) [VAddInvariantMeasure L X μ]
    (P : Set X) (hP : IsAddFundamentalDomain L P μ) (hPfin : μ P < ⊤)
    (Ω : T → Set X) (hΩ : MeasurableSet {p : T × X | p.2 ∈ Ω p.1})
    (hvol : ∀ t, μ (Ω t) ≠ ⊤)
    (V : T × X → Finset L)
    (hV : ∀ t r l, l ∈ V (t,r) ↔ (l : X) + r ∈ Ω t)
    (D : Finset L) (φ : L →+ ℂ) (hφ : Function.Injective φ)
    (hD : ∀ β ∈ D, ‖φ β‖ = 1)
    (a B δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hVolpos : 0 < ∫ t, (μ (Ω t)).toReal ∂ν)
    (hoverlap : a * (∫ t, (μ (Ω t)).toReal ∂ν) ≤
      ∫ t, ∑ β ∈ D, (μ (overlapSet (Ω t) (β : X))).toReal ∂ν)
    (hbound : ∀ p, ((V p).card : ℝ) ≤ B) :
    ∃ U : Finset ℂ, 0 < U.card ∧ (U.card : ℝ) ≤ B ∧
      a / (2 * B ^ δ) ≤ unitPairs U / (U.card : ℝ) ^ (1 + δ) := by
  letI : IsFiniteMeasure (μ.restrict P) := ⟨by simpa using hPfin⟩
  let N : T × X → ℝ := fun p => (V p).card
  let E : T × X → ℝ := fun p => (displacementPairs (V p) D).card
  have hNi : Measurable N := by
    have hm := (measurable_family_lattice_count L Ω hΩ).ennreal_toReal
    convert hm using 1
    funext p
    rw [lattice_count_eq_card L (Ω p.1) p.2 (V p) (hV p.1 p.2)]
    simp [N]
  have hEi : Measurable E := by
    have hm := (measurable_family_lattice_edgeCount L Ω hΩ D).ennreal_toReal
    convert hm using 1
    funext p
    rw [lattice_edge_count_eq_card L (Ω p.1) p.2 (V p) D (hV p.1 p.2)]
    simp [E]
  have hNi' : Integrable N (ν.prod (μ.restrict P)) := by
    apply (integrable_const B).mono' hNi.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p => by simpa [N, Real.norm_eq_abs] using hbound p)
  have hEi' : Integrable E (ν.prod (μ.restrict P)) := by
    apply (integrable_const (B^2)).mono' hEi.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro p
    have hcard : (displacementPairs (V p) D).card ≤ (V p).card * (V p).card := by
      exact displacementPairs_card_bound (V p) D
    have hcardR : ((displacementPairs (V p) D).card : ℝ) ≤ ((V p).card : ℝ)^2 := by
      exact_mod_cast (show (displacementPairs (V p) D).card ≤ (V p).card ^ 2 by simpa only [pow_two] using hcard)
    have hb := hbound p
    have hn : (0 : ℝ) ≤ (V p).card := Nat.cast_nonneg _
    simp only [E, Real.norm_eq_abs, Nat.abs_cast]
    nlinarith
  have hΩt (t : T) : MeasurableSet (Ω t) :=
    hΩ.preimage (measurable_const.prodMk measurable_id)
  have hNv : (∫ p, N p ∂ν.prod (μ.restrict P)) = ∫ t, (μ (Ω t)).toReal ∂ν := by
    rw [integral_prod _ hNi']
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t =>
      (lattice_vertex_integral L μ P hP (Ω t) (hΩt t) (fun r => V (t,r)) (hV t) (hvol t)).2)
  have hEv : (∫ p, E p ∂ν.prod (μ.restrict P)) =
      ∫ t, ∑ β ∈ D, (μ (overlapSet (Ω t) (β : X))).toReal ∂ν := by
    rw [integral_prod _ hEi']
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t =>
      (lattice_edge_integral L μ P hP (Ω t) (hΩt t) (fun r => V (t,r)) (hV t) D (hvol t)).2)
  obtain ⟨p, hn, hb, he⟩ := exists_joint_parameter_rpow (ν.prod (μ.restrict P)) N E a B δ
    hNi' hEi' (fun _ => Nat.cast_nonneg _)
    (fun p hz => by
      change ((V p).card : ℝ) = 0 at hz
      have hv : V p = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hz)
      simp [E, hv])
    (by rw [hNv]; exact hVolpos) (by rw [hNv, hEv]; exact hoverlap) ha hδ hbound
  change (0 : ℝ) < (V p).card at hn
  obtain ⟨U, hcard, hu⟩ := project_displacement_graph (V p) D φ hφ (by
    intro x hx y hy hxy
    rw [dist_eq_norm, norm_sub_rev, ← map_sub]
    exact hD _ hxy)
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hcard]; exact_mod_cast hn
  · simpa only [hcard] using hb
  · rw [hcard]
    have hp : 0 < ((V p).card : ℝ) ^ (1 + δ) := Real.rpow_pos_of_pos hn _
    calc
      a / (2 * B ^ δ) = (a / B ^ δ) / 2 := by ring
      _ ≤ (E p / N p ^ (1 + δ)) / 2 := div_le_div_of_nonneg_right he (by norm_num)
      _ = (E p / 2) / N p ^ (1 + δ) := by ring
      _ ≤ unitPairs U / ((V p).card : ℝ) ^ (1 + δ) := div_le_div_of_nonneg_right hu hp.le

end Families

end UnitDistance
