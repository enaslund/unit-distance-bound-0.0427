module

public import UnitDistance.GeometryTransfer

@[expose] public section
set_option backward.privateInPublic true


/-!
# Connecting norm-one cosets to actual overlap integrals

The steps are actual elements of the additive lattice, indexed injectively
by a label, a torsion element, and a logarithmic lattice point. The only
geometric identification assumed is the individual overlap formula for each
such step. A finite truncation is permitted only with an explicit proof that
all omitted logarithmic terms vanish throughout the averaging domain.
-/

open scoped Classical BigOperators ENNReal
open MeasureTheory

namespace UnitDistance

/-- The finite set of actual norm-one steps retained by an overlap support
truncation. Every component of the index retains its mathematical meaning. -/
noncomputable def selectedSteps {Labels Torsion G A : Type*} [Fintype Torsion] [DecidableEq A]
    (s : Finset Labels) (I : Finset G) (step : Labels → Torsion → G → A) : Finset A :=
  (((s ×ˢ (Finset.univ : Finset Torsion)) ×ˢ I).image
    (fun p => step p.1.1 p.1.2 p.2))

section WeightedUnfolding

variable {G H X Labels Torsion : Type*}
  [AddGroup G] [Countable G] [Fintype Torsion]
  [AddGroup H] [MeasurableSpace H] [MeasurableAdd₂ H] [MeasurableNeg H]
  [AddAction G H] [MeasurableConstVAdd G H]
  [AddCommGroup X] [MeasurableSpace X]
  (ν : Measure H) [VAddInvariantMeasure G H ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
  (Q : Set H) (hQ : IsAddFundamentalDomain G Q ν)
  (L : AddSubgroup X) (μ : Measure X) (Ω : H → Set X)
  (s : Finset Labels) (I : Finset G)
  (step : Labels → Torsion → G → L)
  (hstep : Set.InjOn (fun p : (Labels × Torsion) × G => step p.1.1 p.1.2 p.2)
    ↑((s ×ˢ (Finset.univ : Finset Torsion)) ×ˢ I))
  (Φ : Labels → H → ℝ≥0∞) (hΦ : ∀ i, Measurable (Φ i)) (c : Labels → H)
  (hoverlap : ∀ h ∈ Q, ∀ i ∈ s, ∀ τ : Torsion, ∀ l ∈ I,
    μ (overlapSet (Ω h) (step i τ l : X)) = Φ i (c i - (l +ᵥ h)))
  (htail : ∀ h ∈ Q, ∀ i ∈ s, ∀ l ∉ I, Φ i (c i - (l +ᵥ h)) = 0)

omit [Countable G] [MeasurableSpace H] [MeasurableAdd₂ H] [MeasurableNeg H]
  [MeasurableConstVAdd G H] in
include hstep hoverlap htail in
/-- Pointwise identification with actual finite overlap sums. -/
theorem selected_overlap_eq (h : H) (hh : h ∈ Q) :
    ∑ β ∈ selectedSteps s I step, μ (overlapSet (Ω h) (β : X)) =
      ∑ i : s, ∑ _τ : Torsion, ∑' l : G, Φ i (c i - (l +ᵥ h)) := by
  unfold selectedSteps
  rw [Finset.sum_image hstep]
  simp only [Finset.sum_product]
  rw [Finset.sum_coe_sort s (fun i => ∑ _τ : Torsion, ∑' l : G, Φ i (c i - (l +ᵥ h)))]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [tsum_eq_sum (s := I) (fun l hl => htail h hh i hi l hl)]
  exact Finset.sum_congr rfl (fun l hl => hoverlap h hh i hi τ l hl)

include hQ hstep hoverlap htail hΦ in
/-- Tiling of the full logarithmic unit lattice computes the integrated
sum of *actual geometric overlaps*. The exact torsion multiplicity is the
only factor contributed by the logarithmic kernel. -/
theorem selected_overlap_lintegral :
    (∫⁻ h in Q, ∑ β ∈ selectedSteps s I step, μ (overlapSet (Ω h) (β : X)) ∂ν) =
      (Fintype.card Torsion : ℝ≥0∞) * ∑ i ∈ s, ∫⁻ u, Φ i u ∂ν := by
  calc
    _ = ∫⁻ h in Q, ∑ i : s, ∑ _τ : Torsion, ∑' l : G,
        Φ i (c i - (l +ᵥ h)) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem₀ hQ.nullMeasurableSet] with h hh
      exact selected_overlap_eq Q L μ Ω s I step hstep Φ c hoverlap htail h hh
    _ = (Fintype.card Torsion : ℝ≥0∞) * ∑ i : s, ∫⁻ u, Φ i u ∂ν :=
      logarithmic_unfolding_cosets ν Q hQ (fun i : s => Φ i)
        (fun i => hΦ i) (fun i => c i)
    _ = _ := congrArg ((Fintype.card Torsion : ℝ≥0∞) * ·)
      (Finset.sum_coe_sort s (fun i => ∫⁻ u, Φ i u ∂ν))

include hQ hstep hoverlap htail hΦ in
/-- Real-valued form of the exact overlap mass, suitable for joint
Bochner-integral averaging. All finiteness hypotheses concern ordinary
window or profile integrals. -/
theorem selected_overlap_integral
    (hvol : ∀ h, μ (Ω h) ≠ ⊤) (hΦfin : ∀ i ∈ s, (∫⁻ u, Φ i u ∂ν) ≠ ⊤) :
    (∫ h in Q, ∑ β ∈ selectedSteps s I step, (μ (overlapSet (Ω h) (β : X))).toReal ∂ν) =
      (Fintype.card Torsion : ℝ) * ∑ i ∈ s, (∫⁻ u, Φ i u ∂ν).toReal := by
  let O : H → ℝ≥0∞ := fun h => ∑ β ∈ selectedSteps s I step, μ (overlapSet (Ω h) (β : X))
  let F : H → ℝ≥0∞ := fun h => ∑ i : s, ∑ _τ : Torsion, ∑' l : G,
    Φ i (c i - (l +ᵥ h))
  have hF : Measurable F := Finset.measurable_sum _ (fun i _ =>
    Finset.measurable_sum _ (fun _ _ => Measurable.tsum (fun l =>
      (hΦ i).comp (measurable_const.sub (measurable_const_vadd l)))))
  have heq : O =ᵐ[ν.restrict Q] F := by
    filter_upwards [ae_restrict_mem₀ hQ.nullMeasurableSet] with h hh
    exact selected_overlap_eq Q L μ Ω s I step hstep Φ c hoverlap htail h hh
  have hO : AEMeasurable O (ν.restrict Q) := hF.aemeasurable.congr heq.symm
  have hβfin (h : H) (β : L) : μ (overlapSet (Ω h) (β : X)) ≠ ⊤ :=
    ne_top_of_le_ne_top (hvol h) (measure_mono Set.inter_subset_left)
  have hOfin (h : H) : O h < ⊤ :=
    ENNReal.sum_lt_top.mpr (fun β _ => (hβfin h β).lt_top)
  have hval := integral_toReal hO (Filter.Eventually.of_forall hOfin)
  simp only [O] at hval
  rw [selected_overlap_lintegral ν Q hQ L μ Ω s I step hstep Φ hΦ c hoverlap htail,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_sum hΦfin] at hval
  simpa only [ENNReal.toReal_sum (fun β _ => hβfin _ β)] using hval

include hQ hstep hoverlap htail hΦ in
/-- Full geometric transfer for a selected class: actual additive-lattice
windows, exact local overlap identities, full logarithmic unfolding,
finite torsion, one favorable joint parameter, and planar projection. -/
theorem logarithmic_window_transfer
    [MeasurableAdd₂ X] [Countable L]
    [VAddInvariantMeasure L X μ]
    (hQfin : ν Q < ⊤) (hQ0 : ν Q ≠ 0)
    (P : Set X) (hP : IsAddFundamentalDomain L P μ) (hPfin : μ P < ⊤)
    (hΩjoint : MeasurableSet {p : H × X | p.2 ∈ Ω p.1})
    (volume : ℝ≥0∞) (hvolume : ∀ h, μ (Ω h) = volume)
    (hvolume0 : volume ≠ 0) (hvolumefin : volume ≠ ⊤)
    (V : H × X → Finset L)
    (hV : ∀ h r l, l ∈ V (h,r) ↔ (l : X) + r ∈ Ω h)
    (φ : L →+ ℂ) (hφ : Function.Injective φ)
    (hunit : ∀ i ∈ s, ∀ τ : Torsion, ∀ l ∈ I, ‖φ (step i τ l)‖ = 1)
    (B δ : ℝ) (hδ : 0 ≤ δ) (hbound : ∀ p, ((V p).card : ℝ) ≤ B)
    (hΦfin : ∀ i ∈ s, (∫⁻ u, Φ i u ∂ν) ≠ ⊤) :
    ∃ U : Finset ℂ, 0 < U.card ∧ (U.card : ℝ) ≤ B ∧
      ((Fintype.card Torsion : ℝ) * ∑ i ∈ s, (∫⁻ u, Φ i u ∂ν).toReal) /
        (2 * (ν Q).toReal * volume.toReal * B ^ δ) ≤
        unitPairs U / (U.card : ℝ) ^ (1 + δ) := by
  letI : IsFiniteMeasure (ν.restrict Q) := ⟨by simpa using hQfin⟩
  let W : ℝ := (Fintype.card Torsion : ℝ) * ∑ i ∈ s, (∫⁻ u, Φ i u ∂ν).toReal
  let a : ℝ := W / ((ν Q).toReal * volume.toReal)
  have hW : 0 ≤ W := mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg))
  have hR : 0 < (ν Q).toReal := ENNReal.toReal_pos hQ0 hQfin.ne
  have hVol : 0 < volume.toReal := ENNReal.toReal_pos hvolume0 hvolumefin
  have hmass : (∫ h in Q, (μ (Ω h)).toReal ∂ν) = (ν Q).toReal * volume.toReal := by
    simp only [hvolume, integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  have hoverlapmass := selected_overlap_integral ν Q hQ L μ Ω s I step hstep Φ hΦ c hoverlap htail
    (fun h => by rw [hvolume]; exact hvolumefin) hΦfin
  obtain ⟨U, hU0, hUB, hratio⟩ := family_window_transfer L (ν.restrict Q) μ P hP hPfin
    Ω hΩjoint (fun h => by rw [hvolume]; exact hvolumefin) V hV
    (selectedSteps s I step) φ hφ
    (by
      intro β hβ
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hβ
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨hi, hτ⟩ := Finset.mem_product.mp hp1
      exact hunit _ hi _ _ hp2)
    a B δ (div_nonneg hW (mul_pos hR hVol).le) hδ
    (by rw [hmass]; exact mul_pos hR hVol)
    (by
      rw [hmass, hoverlapmass]
      exact (div_mul_cancel₀ W (mul_pos hR hVol).ne').le)
    hbound
  refine ⟨U, hU0, hUB, ?_⟩
  convert hratio using 1
  dsimp only [a, W]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end WeightedUnfolding

section ClassSelection

/-- Weighted finite-class geometric transfer. The class is selected using
the final overlap integrals. Its positive-weight reference label specifies
the finite reciprocal rescaling, so no equidistribution of local unit
images and no independence from a previously selected class are assumed. -/
theorem weighted_geometric_transfer
    {G H X Labels Torsion C : Type*}
    [AddGroup G] [Countable G] [Fintype Torsion]
    [Fintype Labels] [Fintype C] [Nonempty C] [DecidableEq C]
    [AddGroup H] [MeasurableSpace H] [MeasurableAdd₂ H] [MeasurableNeg H]
    [AddAction G H] [MeasurableConstVAdd G H]
    [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]
    (ν : Measure H) [VAddInvariantMeasure G H ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (Q : Set H) (hQ : IsAddFundamentalDomain G Q ν) (hQfin : ν Q < ⊤) (hQ0 : ν Q ≠ 0)
    (L : AddSubgroup X) [Countable L]
    (μ : Measure X) [VAddInvariantMeasure L X μ]
    (P : Set X) (hP : IsAddFundamentalDomain L P μ) (hPfin : μ P < ⊤)
    (classOf : Labels → C) (I : Finset G)
    (Ω : Labels → H → Set X)
    (hΩjoint : ∀ i₀, MeasurableSet {p : H × X | p.2 ∈ Ω i₀ p.1})
    (volume : ℝ≥0∞) (hvolume : ∀ i₀ h, μ (Ω i₀ h) = volume)
    (hvolume0 : volume ≠ 0) (hvolumefin : volume ≠ ⊤)
    (V : Labels → H × X → Finset L)
    (hV : ∀ i₀ h r l, l ∈ V i₀ (h,r) ↔ (l : X) + r ∈ Ω i₀ h)
    (step : Labels → Labels → Torsion → G → L)
    (hstep : ∀ i₀, Set.InjOn
      (fun p : (Labels × Torsion) × G => step i₀ p.1.1 p.1.2 p.2)
      ↑(((Finset.univ.filter (fun i => classOf i = classOf i₀)) ×ˢ
        (Finset.univ : Finset Torsion)) ×ˢ I))
    (Φ : Labels → H → ℝ≥0∞) (hΦ : ∀ i, Measurable (Φ i))
    (c : Labels → Labels → H)
    (hoverlap : ∀ i₀ h, h ∈ Q → ∀ i, classOf i = classOf i₀ → ∀ τ : Torsion, ∀ l ∈ I,
      μ (overlapSet (Ω i₀ h) (step i₀ i τ l : X)) = Φ i (c i₀ i - (l +ᵥ h)))
    (htail : ∀ i₀ h, h ∈ Q → ∀ i, classOf i = classOf i₀ → ∀ l ∉ I,
      Φ i (c i₀ i - (l +ᵥ h)) = 0)
    (φ : L →+ ℂ) (hφ : Function.Injective φ)
    (hunit : ∀ i₀ i, classOf i = classOf i₀ → ∀ τ : Torsion, ∀ l ∈ I,
      ‖φ (step i₀ i τ l)‖ = 1)
    (B δ : ℝ) (hδ : 0 ≤ δ) (hbound : ∀ i₀ p, ((V i₀ p).card : ℝ) ≤ B)
    (hΦfin : ∀ i, (∫⁻ u, Φ i u ∂ν) ≠ ⊤)
    (hWpos : 0 < ∑ i : Labels, (∫⁻ u, Φ i u ∂ν).toReal) :
    ∃ U : Finset ℂ, 0 < U.card ∧ (U.card : ℝ) ≤ B ∧
      ((Fintype.card Torsion : ℝ) * ∑ i : Labels, (∫⁻ u, Φ i u ∂ν).toReal) /
        (2 * (Fintype.card C : ℝ) * (ν Q).toReal * volume.toReal * B ^ δ) ≤
        unitPairs U / (U.card : ℝ) ^ (1 + δ) := by
  obtain ⟨cl, hmass, i₀, _, hi₀, hi₀pos⟩ := weighted_class_selection Finset.univ classOf
    (fun i => (∫⁻ u, Φ i u ∂ν).toReal) (fun _ _ => ENNReal.toReal_nonneg) hWpos
  let s := Finset.univ.filter (fun i => classOf i = classOf i₀)
  have hmass' : (∑ i : Labels, (∫⁻ u, Φ i u ∂ν).toReal) / Fintype.card C ≤
      ∑ i ∈ s, (∫⁻ u, Φ i u ∂ν).toReal := by
    simpa only [s, hi₀] using hmass
  obtain ⟨U, hU0, hUB, hratio⟩ := logarithmic_window_transfer ν Q hQ L μ (Ω i₀) s I
    (step i₀) (hstep i₀) Φ hΦ (c i₀)
    (fun h hh i hi τ l hl => hoverlap i₀ h hh i (Finset.mem_filter.mp hi).2 τ l hl)
    (fun h hh i hi l hl => htail i₀ h hh i (Finset.mem_filter.mp hi).2 l hl)
    hQfin hQ0 P hP hPfin (hΩjoint i₀) volume (hvolume i₀) hvolume0 hvolumefin
    (V i₀) (hV i₀) φ hφ
    (fun i hi τ l hl => hunit i₀ i (Finset.mem_filter.mp hi).2 τ l hl)
    B δ hδ (hbound i₀) (fun i _ => hΦfin i)
  refine ⟨U, hU0, hUB, le_trans ?_ hratio⟩
  have hB : 0 < B := lt_of_lt_of_le (by exact_mod_cast hU0) hUB
  have hden : 0 ≤ 2 * (ν Q).toReal * volume.toReal * B ^ δ := by positivity
  have hle := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass' (Nat.cast_nonneg (Fintype.card Torsion))) hden
  convert hle using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end ClassSelection

end UnitDistance
