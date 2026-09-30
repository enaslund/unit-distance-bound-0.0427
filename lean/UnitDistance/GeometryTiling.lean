module

public import UnitDistance.GeometryUnfolding
public import UnitDistance.GeometryProjection

@[expose] public section
set_option backward.privateInPublic true


/-!
# Additive translation averages for genuine lattice configurations

The vertex and edge integrands are countable sums of measurable indicators.
The edge identity counts each allowed lattice displacement once. Tiling
therefore gives the volume and overlap integrals, including measurable
window boundaries, before any favorable translate is selected.
-/

open scoped Classical BigOperators ENNReal Pointwise
open MeasureTheory

namespace UnitDistance

section AdditiveTiling

variable {X : Type*} [AddCommGroup X] [MeasurableSpace X]
  [MeasurableAdd₂ X]
  (L : AddSubgroup X) [Countable L]
  (μ : Measure X)
  [VAddInvariantMeasure L X μ]
  (P : Set X) (hP : IsAddFundamentalDomain L P μ)
  (Ω : Set X) (hΩ : MeasurableSet Ω)

/-- The actual number of lattice points in a translated measurable window,
possibly infinite before compactness/discreteness is supplied. -/
noncomputable def translatedLatticeCount (h : X) : ℝ≥0∞ :=
  ∑' l : L, Ω.indicator (fun _ => (1 : ℝ≥0∞)) ((l : X) + h)

/-- The overlap corresponding to one lattice displacement. -/
def overlapSet (β : X) : Set X := Ω ∩ {x | x + β ∈ Ω}

/-- The actual number of inherited ordered lattice edges. -/
noncomputable def translatedLatticeEdgeCount (D : Finset L) (h : X) : ℝ≥0∞ :=
  ∑ β ∈ D, ∑' l : L,
    (overlapSet Ω (β : X)).indicator (fun _ => (1 : ℝ≥0∞)) ((l : X) + h)

include hΩ in
theorem measurable_overlapSet (β : X) : MeasurableSet (overlapSet Ω β) :=
  hΩ.inter (hΩ.preimage (measurable_id.add_const β))

include hP hΩ in
/-- Additive averaging counts vertices with the covolume normalization
`μ P`; dividing this identity by `μ P` gives the probability average. -/
theorem lattice_vertex_average :
    (∫⁻ h in P, translatedLatticeCount L Ω h ∂μ) = μ Ω := by
  simp only [translatedLatticeCount]
  calc
    _ = ∫⁻ x, Ω.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
      logarithmic_unfolding μ P hP _ (measurable_const.indicator hΩ)
    _ = μ Ω := by simp [lintegral_indicator hΩ]

include hP hΩ in
/-- The same additive translation parameter gives the exact ordered-edge
average, as a sum of ordinary overlap volumes. -/
theorem lattice_edge_average (D : Finset L) :
    (∫⁻ h in P, translatedLatticeEdgeCount L Ω D h ∂μ) =
      ∑ β ∈ D, μ (overlapSet Ω (β : X)) := by
  have hm (β : L) : Measurable (fun h => ∑' l : L,
      (overlapSet Ω (β : X)).indicator (fun _ => (1 : ℝ≥0∞)) ((l : X) + h)) :=
    Measurable.tsum (fun l =>
      (measurable_const.indicator (measurable_overlapSet Ω hΩ β)).comp
        (measurable_const.add measurable_id))
  simp only [translatedLatticeEdgeCount]
  rw [lintegral_finsetSum _ (fun β _ => hm β)]
  apply Finset.sum_congr rfl
  intro β hβ
  exact lattice_vertex_average L μ P hP (overlapSet Ω β) (measurable_overlapSet Ω hΩ β)

omit [MeasurableSpace X] [MeasurableAdd₂ X] [Countable L] in
/-- A finite window description is an ordinary membership equality; this
lemma connects its genuine cardinality to the indicator sum in tiling. -/
theorem lattice_count_eq_card (h : X) (V : Finset L)
    (hV : ∀ l : L, l ∈ V ↔ (l : X) + h ∈ Ω) :
    translatedLatticeCount L Ω h = (V.card : ℝ≥0∞) := by
  classical
  unfold translatedLatticeCount
  rw [tsum_eq_sum (s := V)]
  · simp only [← hV, Set.indicator_apply]
    simp
  · intro l hl
    simp [← hV, hl]

omit [MeasurableSpace X] [MeasurableAdd₂ X] [Countable L] in
/-- With a finite window, inherited displacement edges in the abstract
lattice are exactly the points counted by the overlap indicators. -/
theorem lattice_edge_count_eq_card (h : X) (V D : Finset L)
    (hV : ∀ l : L, l ∈ V ↔ (l : X) + h ∈ Ω) :
    translatedLatticeEdgeCount L Ω D h =
      ((displacementPairs V D).card : ℝ≥0∞) := by
  classical
  have hfinite (β : L) : (∑' l : L,
      (overlapSet Ω (β : X)).indicator (fun _ => (1 : ℝ≥0∞)) ((l : X) + h)) =
      ((V.filter (fun l => l + β ∈ V)).card : ℝ≥0∞) := by
    rw [tsum_eq_sum (s := V.filter (fun l => l + β ∈ V))]
    · calc
        _ = ∑ l ∈ V.filter (fun l => l + β ∈ V), (1 : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro l hl
          obtain ⟨hlV, hladd⟩ := Finset.mem_filter.mp hl
          apply Set.indicator_of_mem
          refine ⟨(hV l).mp hlV, ?_⟩
          have hmem := (hV (l + β)).mp hladd
          change (l : X) + h + β ∈ Ω
          simpa only [AddSubgroup.coe_add, add_assoc, add_comm h (β : X)] using hmem
        _ = _ := by simp
    · intro l hl
      apply Set.indicator_of_notMem
      intro hmem
      apply hl
      apply Finset.mem_filter.mpr
      refine ⟨(hV l).mpr hmem.1, (hV (l + β)).mpr ?_⟩
      have hmem' := hmem.2
      change (l : X) + h + (β : X) ∈ Ω at hmem'
      simpa only [AddSubgroup.coe_add, add_assoc, add_comm h (β : X)] using hmem'
  unfold translatedLatticeEdgeCount
  simp_rw [hfinite]
  have hcard : (displacementPairs V D).card =
      ∑ β ∈ D, (V.filter (fun l => l + β ∈ V)).card := by
    rw [← Finset.card_sigma]
    symm
    apply Finset.card_bij (fun p _ => (p.2, p.2 + p.1))
    · intro p hp
      obtain ⟨hpD, hpV⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hpV, hpadd⟩ := Finset.mem_filter.mp hpV
      simp only [displacementPairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hpV, hpadd⟩, by simpa using hpD⟩
    · intro p hp q hq hpq
      have hsecond : p.2 = q.2 := congrArg Prod.fst hpq
      have hfirst : p.1 = q.1 := by
        have heq := congrArg Prod.snd hpq
        dsimp at heq
        rw [hsecond] at heq
        exact add_left_cancel heq
      exact Sigma.ext hfirst (heq_of_eq hsecond)
    · intro e he
      have he' : e ∈ V ×ˢ V ∧ e.2 - e.1 ∈ D := by
        simpa only [displacementPairs, Finset.mem_filter] using he
      obtain ⟨heV, heD⟩ := he'
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp heV
      refine ⟨⟨e.2 - e.1, e.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_filter]
        exact ⟨heD, hx, by simpa [add_sub_cancel_left] using hy⟩
      · simp
  exact_mod_cast hcard.symm

end AdditiveTiling

end UnitDistance
