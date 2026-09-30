module

public import UnitDistance.GeometryWeighted
public import UnitDistance.SupportedProfile
public import UnitDistance.Asymptotic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Energy profiles and the weighted geometric transfer

This file connects the displacement-position overlap law with the same
individual overlap profiles used by the weighted class transfer.
-/

open scoped Classical BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace UnitDistance

/-- The ordinary overlap-volume function is measurable in a measurable
family of actual displacements. -/
theorem measurable_overlap_volume {D X : Type*} [MeasurableSpace D]
    [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]
    (μ : Measure X) [SFinite μ] (Ω : Set X) (hΩ : MeasurableSet Ω)
    (step : D → X) (hstep : Measurable step) :
    Measurable (fun β => μ (overlapSet Ω (step β))) := by
  have hs : MeasurableSet {p : D × X | p.2 ∈ Ω ∧ p.2 + step p.1 ∈ Ω} :=
    (hΩ.preimage measurable_snd).inter
      (hΩ.preimage (measurable_snd.add (hstep.comp measurable_fst)))
  exact measurable_measure_prodMk_left hs

/-- Counting measure on the finite valuation labels, and additive Haar
measure on pair logarithms, give exactly the sum of local overlap integrals.
There is no extra angular or unit-group cardinality factor. -/
theorem labeled_overlap_integral {Labels H X : Type*}
    [Fintype Labels] [MeasurableSpace Labels] [MeasurableSingletonClass Labels]
    [MeasurableSpace H] [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]
    (ν : Measure H) [SFinite ν] (μ : Measure X) [SFinite μ]
    (Ω : Set X) (hΩ : MeasurableSet Ω)
    (step : Labels × H → X) (hstep : Measurable step) :
    (∫⁻ β, μ (overlapSet Ω (step β)) ∂(Measure.count.prod ν)) =
      ∑ i : Labels, ∫⁻ u, μ (overlapSet Ω (step (i,u))) ∂ν := by
  rw [lintegral_prod _ (measurable_overlap_volume μ Ω hΩ step hstep).aemeasurable,
    lintegral_count, tsum_fintype]

/-- Real-valued overlap assembly from exactly the preceding measure identity. -/
theorem labeled_overlap_toReal {Labels H X : Type*}
    [Fintype Labels] [MeasurableSpace Labels] [MeasurableSingletonClass Labels]
    [MeasurableSpace H] [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]
    (ν : Measure H) [SFinite ν] (μ : Measure X) [SFinite μ]
    (Ω : Set X) (hΩ : MeasurableSet Ω)
    (step : Labels × H → X) (hstep : Measurable step)
    (hfin : (∫⁻ β, μ (overlapSet Ω (step β)) ∂(Measure.count.prod ν)) ≠ ⊤) :
    (∫⁻ β, μ (overlapSet Ω (step β)) ∂(Measure.count.prod ν)).toReal =
      ∑ i : Labels, (∫⁻ u, μ (overlapSet Ω (step (i,u))) ∂ν).toReal := by
  rw [labeled_overlap_integral ν μ Ω hΩ step hstep] at hfin ⊢
  apply ENNReal.toReal_sum
  intro i hi
  exact ne_top_of_le_ne_top hfin
    (Finset.single_le_sum (f := fun j : Labels => ∫⁻ u, μ (overlapSet Ω (step (j,u))) ∂ν)
      (fun _ _ => bot_le) hi)

/-- Positive overlap mass forces the original window to have positive
ordinary Haar volume; no separate nonvacuity hypothesis is needed. -/
theorem window_measure_ne_zero_of_overlap_pos {D X : Type*}
    [MeasurableSpace D] [AddCommGroup X] [MeasurableSpace X]
    (σ : Measure D) (μ : Measure X) (Ω : Set X) (step : D → X)
    (hpos : 0 < (∫⁻ β, μ (overlapSet Ω (step β)) ∂σ).toReal) : μ Ω ≠ 0 := by
  intro hzero
  have hβ : ∀ β, μ (overlapSet Ω (step β)) = 0 :=
    fun β => measure_mono_null Set.inter_subset_left hzero
  simp only [hβ, lintegral_zero, ENNReal.toReal_zero, lt_self_iff_false] at hpos

/-- Finite profile mass forces every finite energy sublevel to have finite
Haar volume, also for profiles which vanish off `S`. -/
theorem supported_energy_window_finite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (E : X → ℝ) (p T : ℝ) (hp : 0 ≤ p)
    (hE : Measurable E)
    (hI : Integrable (fun x => Real.exp (-p*E x)) (μ.restrict S)) :
    μ (supportedWindow S E T) ≠ ⊤ := by
  have hs : MeasurableSet {x | E x ≤ T} := measurableSet_le hE measurable_const
  have hsub : {x | E x ≤ T} ⊆ {x | Real.exp (-p*T) ≤ Real.exp (-p*E x)} := by
    intro x hx
    apply Real.exp_le_exp.mpr
    change E x ≤ T at hx
    nlinarith
  have hfin := lt_of_le_of_lt (measure_mono hsub) (hI.measure_ge_lt_top (Real.exp_pos (-p*T)))
  rw [Measure.restrict_apply hs] at hfin
  simpa only [supportedWindow, energyWindow, Set.inter_comm] using hfin.ne

/-- Integrability of the original overlap density also proves finiteness of
the common-window overlap. No compact-support finiteness is assumed here. -/
theorem supported_energy_overlap_finite {D X : Type*}
    [MeasurableSpace D] [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]
    (σ : Measure D) (μ : Measure X) [SFinite μ]
    (step : D → X) (hstep : Measurable step)
    (S : Set X) (hS : MeasurableSet S) (E : X → ℝ) (hE : Measurable E) (T : ℝ)
    (hI : Integrable (fun z : D × X =>
      Real.exp (-(firstEnergy E z + secondEnergy E step z)))
      (supportedOverlapMeasure σ μ step S)) :
    supportedWindowOverlap σ μ step S E T ≠ ⊤ := by
  rw [supportedWindowOverlap_eq_pair_measure σ μ step hstep S hS E hE]
  have hsub : {z : D × X | firstEnergy E z ≤ T ∧ secondEnergy E step z ≤ T} ⊆
      {z | Real.exp (-2*T) ≤ Real.exp (-(firstEnergy E z + secondEnergy E step z))} := by
    intro z hz
    apply Real.exp_le_exp.mpr
    obtain ⟨hx, hy⟩ := hz
    linarith
  exact (lt_of_le_of_lt (measure_mono hsub) (hI.measure_ge_lt_top (Real.exp_pos (-2*T)))).ne

section EnergyModel

variable {G H X Labels Torsion C : Type*}
  [AddGroup G] [Countable G] [Fintype Torsion]
  [Fintype Labels] [Fintype C] [Nonempty C] [DecidableEq C]
  [AddGroup H] [MeasurableSpace H] [MeasurableAdd₂ H] [MeasurableNeg H]
  [AddAction G H] [MeasurableConstVAdd G H]
  [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]

/-- Ordinary geometric realization data for a family of energy windows.
No field stores an edge count, average-degree estimate, or planar conclusion.
`vertices` enumerates exactly the lattice intersection by `membership`;
`compactLatticeWindow` gives a canonical choice for closed discrete lattices.
-/
structure WeightedWindowModel (Q : Set H) (L : AddSubgroup X) (μ : Measure X)
    (baseWindow : Set X) (Φ : Labels → H → ℝ≥0∞) (T : ℝ) where
  classOf : Labels → C
  cutoff : Finset G
  window : Labels → H → Set X
  measurable_window : ∀ i₀, MeasurableSet {p : H × X | p.2 ∈ window i₀ p.1}
  volume_eq : ∀ i₀ h, μ (window i₀ h) = μ baseWindow
  vertices : Labels → H × X → Finset L
  membership : ∀ i₀ h r l, l ∈ vertices i₀ (h,r) ↔ (l : X) + r ∈ window i₀ h
  step : Labels → Labels → Torsion → G → L
  step_injective : ∀ i₀, Set.InjOn
    (fun p : (Labels × Torsion) × G => step i₀ p.1.1 p.1.2 p.2)
    ↑(((Finset.univ.filter (fun i => classOf i = classOf i₀)) ×ˢ
      (Finset.univ : Finset Torsion)) ×ˢ cutoff)
  logShift : Labels → Labels → H
  overlap_eq : ∀ i₀ h, h ∈ Q → ∀ i, classOf i = classOf i₀ → ∀ τ : Torsion, ∀ l ∈ cutoff,
    μ (overlapSet (window i₀ h) (step i₀ i τ l : X)) = Φ i (logShift i₀ i - (l +ᵥ h))
  omitted_overlap : ∀ i₀ h, h ∈ Q → ∀ i, classOf i = classOf i₀ → ∀ l ∉ cutoff,
    Φ i (logShift i₀ i - (l +ᵥ h)) = 0
  plane : L →+ ℂ
  plane_injective : Function.Injective plane
  unit_step : ∀ i₀ i, classOf i = classOf i₀ → ∀ τ : Torsion, ∀ l ∈ cutoff,
    ‖plane (step i₀ i τ l)‖ = 1
  energy : Labels → H → X → ℝ
  energy_le : ∀ i₀ h x, x ∈ window i₀ h → energy i₀ h x ≤ T

/-- Exponential majorization derives the common vertex bound from the
actual weighted lattice sums. The rest of the geometric transfer is then
entirely proved from `WeightedWindowModel`'s ordinary realization data. -/
theorem WeightedWindowModel.energy_transfer
    (ν : Measure H) [VAddInvariantMeasure G H ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (Q : Set H) (hQ : IsAddFundamentalDomain G Q ν) (hQfin : ν Q < ⊤) (hQ0 : ν Q ≠ 0)
    (L : AddSubgroup X) [Countable L]
    (μ : Measure X) [VAddInvariantMeasure L X μ]
    (P : Set X) (hP : IsAddFundamentalDomain L P μ) (hPfin : μ P < ⊤)
    (baseWindow : Set X) (Φ : Labels → H → ℝ≥0∞) (T : ℝ)
    (model : WeightedWindowModel (G := G) (Torsion := Torsion) (C := C) Q L μ baseWindow Φ T)
    (hbase0 : μ baseWindow ≠ 0) (hbasefin : μ baseWindow ≠ ⊤)
    (hΦ : ∀ i, Measurable (Φ i)) (hΦfin : ∀ i, (∫⁻ u, Φ i u ∂ν) ≠ ⊤)
    (A D p δ z : ℝ) (hA : 0 < A) (hD : 0 < D) (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    (hz : 0 < z)
    (hOverlap : z ≤ ∑ i : Labels, (∫⁻ u, Φ i u ∂ν).toReal)
    (hVolume : (μ baseWindow).toReal ≤ A * Real.exp (p*T))
    (hweighted : ∀ i₀ h r,
      ∑ l ∈ model.vertices i₀ (h,r), Real.exp (-p * model.energy i₀ h ((l : X) + r)) ≤ 2*A/D) :
    ∃ U : Finset ℂ, 0 < U.card ∧ (U.card : ℝ) ≤ 2*A*Real.exp (p*T)/D ∧
      (((Fintype.card Torsion : ℝ) / ((Fintype.card C : ℝ) * (ν Q).toReal)) *
        z / (A * Real.exp (p*T))) / (2 * (2*A*Real.exp (p*T)/D)^δ) ≤
        unitPairs U / (U.card : ℝ) ^ (1+δ) := by
  let B := 2*A*Real.exp (p*T)/D
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound : ∀ i₀ p', ((model.vertices i₀ p').card : ℝ) ≤ B := by
    intro i₀ p'
    have hc := energy_window_card (model.vertices i₀ p')
      (fun l : L => model.energy i₀ p'.1 ((l : X) + p'.2)) p T hp
      (fun l hl => model.energy_le i₀ p'.1 _ ((model.membership i₀ p'.1 p'.2 l).mp hl))
    calc
      _ ≤ Real.exp (p*T) * ∑ l ∈ model.vertices i₀ p',
          Real.exp (-p * model.energy i₀ p'.1 ((l : X) + p'.2)) := hc
      _ ≤ Real.exp (p*T) * (2*A/D) :=
        mul_le_mul_of_nonneg_left (hweighted i₀ p'.1 p'.2) (Real.exp_pos _).le
      _ = B := by dsimp [B]; ring
  obtain ⟨U, hU0, hUB, hratio⟩ := weighted_geometric_transfer ν Q hQ hQfin hQ0 L μ P hP hPfin
    model.classOf model.cutoff model.window model.measurable_window (μ baseWindow) model.volume_eq
    hbase0 hbasefin model.vertices model.membership model.step model.step_injective
    Φ hΦ model.logShift model.overlap_eq model.omitted_overlap model.plane model.plane_injective
    model.unit_step B δ hδ hbound hΦfin (lt_of_lt_of_le hz hOverlap)
  refine ⟨U, hU0, hUB, le_trans ?_ hratio⟩
  have hR : 0 < (ν Q).toReal := ENNReal.toReal_pos hQ0 hQfin.ne
  have hClass : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hVol : 0 < (μ baseWindow).toReal := ENNReal.toReal_pos hbase0 hbasefin
  have hmass : 0 ≤ (Fintype.card Torsion : ℝ) / ((Fintype.card C : ℝ) * (ν Q).toReal) := by positivity
  have hpre : ((Fintype.card Torsion : ℝ) / ((Fintype.card C : ℝ) * (ν Q).toReal)) *
        z / (A * Real.exp (p*T)) ≤
      ((Fintype.card Torsion : ℝ) / ((Fintype.card C : ℝ) * (ν Q).toReal)) *
        (∑ i : Labels, (∫⁻ u, Φ i u ∂ν).toReal) / (μ baseWindow).toReal := by
    apply div_le_div₀ (mul_nonneg hmass (hz.le.trans hOverlap)) (mul_le_mul_of_nonneg_left hOverlap hmass) hVol hVolume
  have hden : 0 ≤ 2 * B^δ := by positivity
  have hle := div_le_div_of_nonneg_right hpre hden
  convert hle using 1
  simp only [B, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Principal conditional transfer theorem, including profiles with zeros.
The overlap lower bound, window-volume bound, uniform cardinal bound,
weighted class selection, both tilings, and the final real-power ratio are
all derived. The remaining inputs are exact profile integrals and moments,
the ordinary geometric realization data, and a uniform weighted lattice
sum estimate. This theorem does not assert existence of an arithmetic tower.
-/
theorem supported_energy_geometric_transfer
    [MeasurableSpace Labels] [MeasurableSingletonClass Labels]
    (ν : Measure H) [SFinite ν]
    [VAddInvariantMeasure G H ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (Q : Set H) (hQ : IsAddFundamentalDomain G Q ν) (hQfin : ν Q < ⊤) (hQ0 : ν Q ≠ 0)
    (L : AddSubgroup X) [Countable L]
    (μ : Measure X) [SFinite μ] [VAddInvariantMeasure L X μ]
    (P : Set X) (hP : IsAddFundamentalDomain L P μ) (hPfin : μ P < ⊤)
    (S : Set X) (hS : MeasurableSet S) (E : X → ℝ) (hE : Measurable E)
    (normStep : Labels × H → X) (hNormStep : Measurable normStep)
    (A D p δ Z varianceBound ε d mean : ℝ)
    (hA : 0 < A) (hD : 0 < D) (hZ : 0 < Z) (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    (hpδ : p*(1+δ) = 2) (hε : 0 < ε) (hd : 0 < d)
    (hAI : Integrable (fun x => Real.exp (-p*E x)) (μ.restrict S))
    (hAmass : (∫ x in S, Real.exp (-p*E x) ∂μ) = A)
    (hZI : Integrable (fun z : (Labels × H) × X =>
      Real.exp (-(firstEnergy E z + secondEnergy E normStep z)))
      (supportedOverlapMeasure (Measure.count.prod ν) μ normStep S))
    (hZmass : (∫ z : (Labels × H) × X,
      Real.exp (-(firstEnergy E z + secondEnergy E normStep z))
      ∂supportedOverlapMeasure (Measure.count.prod ν) μ normStep S) = Z)
    (hX : MemLp (firstEnergy E) 2
      (overlapLaw (supportedOverlapMeasure (Measure.count.prod ν) μ normStep S)
        (firstEnergy E) (secondEnergy E normStep) Z))
    (hY : MemLp (secondEnergy E normStep) 2
      (overlapLaw (supportedOverlapMeasure (Measure.count.prod ν) μ normStep S)
        (firstEnergy E) (secondEnergy E normStep) Z))
    (hmeanX : (∫ z, firstEnergy E z
      ∂overlapLaw (supportedOverlapMeasure (Measure.count.prod ν) μ normStep S)
        (firstEnergy E) (secondEnergy E normStep) Z) = mean)
    (hmeanY : (∫ z, secondEnergy E normStep z
      ∂overlapLaw (supportedOverlapMeasure (Measure.count.prod ν) μ normStep S)
        (firstEnergy E) (secondEnergy E normStep) Z) = mean)
    (hvX : variance (firstEnergy E)
      (overlapLaw (supportedOverlapMeasure (Measure.count.prod ν) μ normStep S)
        (firstEnergy E) (secondEnergy E normStep) Z) ≤ varianceBound*d)
    (hvY : variance (secondEnergy E normStep)
      (overlapLaw (supportedOverlapMeasure (Measure.count.prod ν) μ normStep S)
        (firstEnergy E) (secondEnergy E normStep) Z) ≤ varianceBound*d)
    (hlarge : 4*varianceBound ≤ ε^2*d)
    (model : WeightedWindowModel (G := G) (Torsion := Torsion) (C := C) Q L μ
      (supportedWindow S E (mean+ε*d))
      (fun i u => μ (overlapSet (supportedWindow S E (mean+ε*d)) (normStep (i,u))))
      (mean+ε*d))
    (hweighted : ∀ i₀ h r,
      ∑ l ∈ model.vertices i₀ (h,r), Real.exp (-p * model.energy i₀ h ((l : X) + r)) ≤ 2*A/D) :
    ∃ U : Finset ℂ, 0 < U.card ∧ (U.card : ℝ) ≤ 2*A*Real.exp (p*(mean+ε*d))/D ∧
      ((Fintype.card Torsion : ℝ) / ((Fintype.card C : ℝ) * (ν Q).toReal)) *
        D^δ / (2:ℝ)^(2+δ) * (Z/A^(1+δ)) * Real.exp (-4*(ε*d)) ≤
        unitPairs U / (U.card : ℝ) ^ (1+δ) := by
  let Ω := supportedWindow S E (mean+ε*d)
  let Φ : Labels → H → ℝ≥0∞ := fun i u => μ (overlapSet Ω (normStep (i,u)))
  have hΩ : MeasurableSet Ω := measurableSet_supportedWindow hS hE _
  have hΦ : ∀ i, Measurable (Φ i) := fun i =>
    (measurable_overlap_volume μ Ω hΩ normStep hNormStep).comp
      (measurable_const.prodMk measurable_id)
  have htotalfin := supported_energy_overlap_finite (Measure.count.prod ν) μ normStep hNormStep
    S hS E hE (mean+ε*d) hZI
  have hconcentration := concentrated_supportedWindowOverlap (Measure.count.prod ν) μ normStep hNormStep
    S hS E hE hZ hZI hZmass hX hY hmeanX hmeanY hε hd hvX hvY hlarge htotalfin
  have hsum := labeled_overlap_toReal ν μ Ω hΩ normStep hNormStep htotalfin
  have hsumfin : (∑ i : Labels, ∫⁻ u, Φ i u ∂ν) ≠ ⊤ := by
    rw [← labeled_overlap_integral ν μ Ω hΩ normStep hNormStep]
    exact htotalfin
  have hΦfin : ∀ i, (∫⁻ u, Φ i u ∂ν) ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top hsumfin
      (Finset.single_le_sum (f := fun j : Labels => ∫⁻ u, Φ j u ∂ν)
        (fun _ _ => bot_le) (Finset.mem_univ i))
  have hz : (0 : ℝ) < (1/2)*Z*Real.exp (2*(mean-ε*d)) := by positivity
  have htotalpos : 0 < (∫⁻ β, μ (overlapSet Ω (normStep β)) ∂Measure.count.prod ν).toReal :=
    lt_of_lt_of_le hz hconcentration
  have hbase0 := window_measure_ne_zero_of_overlap_pos (Measure.count.prod ν) μ Ω normStep htotalpos
  have hbasefin := supported_energy_window_finite μ S E p (mean+ε*d) hp hE hAI
  have hVolume : (μ Ω).toReal ≤ A * Real.exp (p*(mean+ε*d)) := by
    have hb := supported_energy_window_volume μ S E p (mean+ε*d) hp hE hAI hbasefin
    rw [hAmass] at hb
    simpa only [Measure.real, mul_comm] using hb
  obtain ⟨U, hU0, hUB, hratio⟩ := model.energy_transfer ν Q hQ hQfin hQ0 L μ P hP hPfin
    Ω Φ (mean+ε*d) hbase0 hbasefin hΦ hΦfin A D p δ
    ((1/2)*Z*Real.exp (2*(mean-ε*d))) hA hD hp hδ hz
    (by rw [← hsum]; exact hconcentration) hVolume hweighted
  refine ⟨U, hU0, hUB, ?_⟩
  have hid := weighted_ratio_identity
    ((Fintype.card Torsion : ℝ) / ((Fintype.card C : ℝ) * (ν Q).toReal))
    Z A D p δ mean (ε*d) hA hD hpδ
  rw [← hid]
  convert hratio using 1
  ring

end EnergyModel

end UnitDistance
