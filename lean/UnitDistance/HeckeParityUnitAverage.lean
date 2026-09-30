module

public import UnitDistance.HeckeParityAverage

@[expose] public section
set_option backward.privateInPublic true


open Complex Set Filter Asymptotics MeasureTheory
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Topology Real nonZeroDivisors Classical
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis

variable (K : Type*) [Field K] [NumberField K]

/-- The actual Dirichlet-unit fundamental box used in the Dedekind-zeta theta construction. -/
noncomputable def heckeUnitBox : Set (logSpace K) :=
  ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ)

theorem measurableSet_heckeUnitBox : MeasurableSet (heckeUnitBox K) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem heckeUnitBox_measure_ne_top : volume (heckeUnitBox K) ≠ ⊤ :=
  ne_top_of_lt (ZSpan.fundamentalDomain_isBounded _).measure_lt_top

/-- Actual upper bound complementary to the upstream lower Hecke-weight bound. -/
theorem heckeWeights_le_of_bounded {R : ℝ} (hR : 0 ≤ R) {u : logSpace K}
    (hu : ∀ i, |u i| ≤ R) {t : ℝ} (ht : 0 ≤ t) (w : InfinitePlace K) :
    DedekindResidue.heckeWeights K t u w ≤
      Real.exp (2 * (Fintype.card (InfinitePlace K)) * R) *
        t ^ ((1 : ℝ) / (Module.finrank ℚ K)) := by
  rw [DedekindResidue.heckeWeights, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht _)
  apply Real.exp_le_exp.mpr
  have habs := DedekindResidue.abs_fullLog_le K hR hu w
  have hmult1 : (1 : ℝ) ≤ (InfinitePlace.mult w : ℝ) := by
    have := InfinitePlace.mult_pos (w := w)
    exact_mod_cast this
  have hmultpos : (0 : ℝ) < InfinitePlace.mult w := lt_of_lt_of_le one_pos hmult1
  apply (div_le_iff₀ hmultpos).mpr
  calc
    2 * DedekindResidue.fullLog K u w ≤ 2 * |DedekindResidue.fullLog K u w| := by
      linarith [le_abs_self (DedekindResidue.fullLog K u w)]
    _ ≤ 2 * (Fintype.card (InfinitePlace K)) * R := by linarith
    _ ≤ (2 * (Fintype.card (InfinitePlace K)) * R) * InfinitePlace.mult w := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * (Fintype.card (InfinitePlace K)) by positivity) hR]

theorem continuous_heckeWeights_log (t : ℝ) (w : InfinitePlace K) :
    Continuous (fun u : logSpace K => DedekindResidue.heckeWeights K t u w) := by
  unfold DedekindResidue.heckeWeights
  exact continuous_const.mul
    (Real.continuous_exp.comp ((continuous_const.mul (DedekindResidue.continuous_fullLog K w)).div_const _))

theorem continuousOn_heckeWeights_radial (u : logSpace K) (w : InfinitePlace K) :
    ContinuousOn (fun t : ℝ => DedekindResidue.heckeWeights K t u w) (Ioi 0) := by
  unfold DedekindResidue.heckeWeights
  exact (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))).mul continuousOn_const

/-- Unit-box average of the actual parity lattice theta with the actual Hecke weights. -/
noncomputable def heckeParityUnitAverage (p : NumberField.mixedEmbedding.index K → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ (NumberField.mixedEmbedding.index K))) (t : ℝ) : ℂ :=
  ∫ u in heckeUnitBox K,
    heckeParityTheta p L (DedekindResidue.placeWeights K (DedekindResidue.heckeWeights K t u))

/-- The actual unit-box average has an entire Mellin transform whenever one coordinate is odd.
No supplied decay, theta functional equation, or Mellin holomorphy hypothesis is used. -/
theorem differentiable_mellin_heckeParityUnitAverage
    (p : NumberField.mixedEmbedding.index K → Bool) (hp : ∃ i, p i = true)
    (L : Submodule ℤ (EuclideanSpace ℝ (NumberField.mixedEmbedding.index K)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    Differentiable ℂ (mellin (heckeParityUnitAverage K p L)) := by
  classical
  let B := heckeUnitBox K
  let μ : Measure B := (volume.restrict B).comap Subtype.val
  let W : ℝ → B → NumberField.mixedEmbedding.index K → ℝ := fun t u =>
    DedekindResidue.placeWeights K (DedekindResidue.heckeWeights K t u)
  haveI : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr (heckeUnitBox_measure_ne_top K)
  haveI : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure ((volume.restrict B).comap Subtype.val))
  have havg : heckeParityAverage p L W μ = heckeParityUnitAverage K p L := by
    funext t
    unfold heckeParityAverage heckeParityUnitAverage
    change (∫ u : B, heckeParityTheta p L
      (DedekindResidue.placeWeights K (DedekindResidue.heckeWeights K t (u : logSpace K)))
      ∂((volume.restrict B).comap Subtype.val)) = _
    have hi := integral_subtype_comap (μ := volume.restrict B)
      (s := B) (show MeasurableSet B from measurableSet_heckeUnitBox K)
      (fun u : logSpace K => heckeParityTheta p L
        (DedekindResidue.placeWeights K (DedekindResidue.heckeWeights K t u)))
    simpa only [Measure.restrict_restrict (show MeasurableSet B from measurableSet_heckeUnitBox K),
      inter_self] using hi
  rw [← havg]
  obtain ⟨R, hR, hbox⟩ := DedekindResidue.exists_box_coord_bound K
  apply differentiable_mellin_heckeParityAverage p hp L W μ
    (r := (1 : ℝ) / Module.finrank ℚ K)
    (m := Real.exp (-(2 * (Fintype.card (InfinitePlace K)) * R)))
    (M := Real.exp (2 * (Fintype.card (InfinitePlace K)) * R))
    (by exact one_div_pos.mpr (DedekindResidue.finrank_pos_real K))
    (Real.exp_pos _) (Real.exp_pos _)
  · intro t ht u
    rintro (w | ⟨w, j⟩) <;> exact DedekindResidue.heckeWeights_pos K ht u w
  · intro t ht
    rintro (w | ⟨w, j⟩) <;>
      exact (continuous_heckeWeights_log K t w).comp continuous_subtype_val
  · intro u
    rintro (w | ⟨w, j⟩) <;> exact continuousOn_heckeWeights_radial K u w
  · intro t ht u
    rintro (w | ⟨w, j⟩) <;>
      exact DedekindResidue.le_heckeWeights_of_bounded K hR (hbox u u.property) ht.le w
  · intro t ht u
    rintro (w | ⟨w, j⟩) <;>
      exact heckeWeights_le_of_bounded K hR (hbox u u.property) ht.le w
  · intro t ht u
    exact DedekindResidue.prod_placeWeights_heckeWeights K ht u

/-- Absolute convergence of the actual unit-box Mellin integral at every complex parameter. -/
theorem mellinConvergent_heckeParityUnitAverage
    (p : NumberField.mixedEmbedding.index K → Bool) (hp : ∃ i, p i = true)
    (L : Submodule ℤ (EuclideanSpace ℝ (NumberField.mixedEmbedding.index K)))
    [DiscreteTopology L] [IsZLattice ℝ L] (s : ℂ) :
    MellinConvergent (heckeParityUnitAverage K p L) s := by
  classical
  let B := heckeUnitBox K
  let μ : Measure B := (volume.restrict B).comap Subtype.val
  let W : ℝ → B → NumberField.mixedEmbedding.index K → ℝ := fun t u =>
    DedekindResidue.placeWeights K (DedekindResidue.heckeWeights K t u)
  haveI : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr (heckeUnitBox_measure_ne_top K)
  haveI : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure ((volume.restrict B).comap Subtype.val))
  have havg : heckeParityAverage p L W μ = heckeParityUnitAverage K p L := by
    funext t
    unfold heckeParityAverage heckeParityUnitAverage
    change (∫ u : B, heckeParityTheta p L
      (DedekindResidue.placeWeights K (DedekindResidue.heckeWeights K t (u : logSpace K)))
      ∂((volume.restrict B).comap Subtype.val)) = _
    have hi := integral_subtype_comap (μ := volume.restrict B)
      (s := B) (show MeasurableSet B from measurableSet_heckeUnitBox K)
      (fun u : logSpace K => heckeParityTheta p L
        (DedekindResidue.placeWeights K (DedekindResidue.heckeWeights K t u)))
    simpa only [Measure.restrict_restrict (show MeasurableSet B from measurableSet_heckeUnitBox K),
      inter_self] using hi
  rw [← havg]
  obtain ⟨R, hR, hbox⟩ := DedekindResidue.exists_box_coord_bound K
  apply mellinConvergent_heckeParityAverage p hp L W μ (s := s)
    (r := (1 : ℝ) / Module.finrank ℚ K)
    (m := Real.exp (-(2 * (Fintype.card (InfinitePlace K)) * R)))
    (M := Real.exp (2 * (Fintype.card (InfinitePlace K)) * R))
    (by exact one_div_pos.mpr (DedekindResidue.finrank_pos_real K))
    (Real.exp_pos _) (Real.exp_pos _)
  · intro t ht u
    rintro (w | ⟨w, j⟩) <;> exact DedekindResidue.heckeWeights_pos K ht u w
  · intro t ht
    rintro (w | ⟨w, j⟩) <;>
      exact (continuous_heckeWeights_log K t w).comp continuous_subtype_val
  · intro u
    rintro (w | ⟨w, j⟩) <;> exact continuousOn_heckeWeights_radial K u w
  · intro t ht u
    rintro (w | ⟨w, j⟩) <;>
      exact DedekindResidue.le_heckeWeights_of_bounded K hR (hbox u u.property) ht.le w
  · intro t ht u
    rintro (w | ⟨w, j⟩) <;>
      exact heckeWeights_le_of_bounded K hR (hbox u u.property) ht.le w
  · intro t ht u
    exact DedekindResidue.prod_placeWeights_heckeWeights K ht u

end UnitDistance.NumberFieldAnalysis
