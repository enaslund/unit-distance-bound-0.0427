module

public import UnitDistance.RelativeUnitsDifference

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual relative difference lattice and regulator

Discreteness is proved by bounding every archimedean absolute value of an
actual relative unit and applying finiteness of algebraic integers of bounded
conjugates. Fullness follows from the proved relative-unit rank and torsion kernel.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace NumberField.Units

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

/-- All archimedean logarithms of a norm-one unit are bounded by its actual
relative-coordinate sup norm. -/
theorem log_place_le_difference_norm (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (u : Additive (normOneUnits (F := F) (K := K))) (v : InfinitePlace K) :
    |Real.log (v u.toMul.val)| ≤ ‖relativeDifferenceLog ι u‖ := by
  obtain ⟨a, rfl⟩ := pairedPlace_surjective ι hι v
  rcases a with w | ⟨w, b⟩
  · rw [show pairedPlace ι (Sum.inl w) = chosenPlaceAbove w.val from rfl,
      log_real_place_normOne ι hι, abs_zero]
    exact norm_nonneg _
  · have hn : |Real.log (chosenPlaceAbove (K := K) w.val u.toMul.val)| ≤
        ‖relativeDifferenceLog ι u‖ := by
      rw [← relativeDifferenceLog_apply ι hι]
      exact norm_le_pi_norm (relativeDifferenceLog ι u) w
    cases b
    · exact hn
    · have hp := log_pair_sum_normOne ι hι (chosenPlaceAbove w.val) u.toMul
      have he : Real.log ((ι • chosenPlaceAbove (K := K) w.val) u.toMul.val) =
          -Real.log (chosenPlaceAbove (K := K) w.val u.toMul.val) := by linarith
      change |Real.log ((ι • chosenPlaceAbove (K := K) w.val) u.toMul.val)| ≤ _
      rw [he, abs_neg]
      exact hn

/-- Bounded relative logarithmic coordinates contain only finitely many actual units. -/
theorem bounded_relative_units_finite (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (r : ℝ) :
    {u : Additive (normOneUnits (F := F) (K := K)) |
      ‖relativeDifferenceLog ι u‖ ≤ r}.Finite := by
  let f : Additive (normOneUnits (F := F) (K := K)) → K := fun u ↦ u.toMul.val
  have hf : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    exact Units.coe_injective K h
  apply Set.Finite.of_finite_image (f := f) _ hf.injOn
  apply (Embeddings.finite_of_norm_le K ℂ (Real.exp r)).subset
  rintro x ⟨u, hu, rfl⟩
  refine ⟨u.toMul.val.val.prop, (le_iff_le _ _).mp ?_⟩
  intro v
  apply (Real.log_le_iff_le_exp (Units.pos_at_place _ _)).mp
  exact (le_abs_self _).trans ((log_place_le_difference_norm ι hι u v).trans hu)

/-- The manuscript's actual lattice in its `c` unweighted difference coordinates. -/
def differenceLattice (ι : K ≃ₐ[F] K) :
    Submodule ℤ ({w : InfinitePlace F // IsComplex w} → ℝ) :=
  (relativeDifferenceLog ι).toIntLinearMap.range

/-- Its intersection with every bounded coordinate ball is finite. -/
theorem differenceLattice_inter_ball_finite (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (r : ℝ) :
    ((differenceLattice ι : Set ({w : InfinitePlace F // IsComplex w} → ℝ)) ∩
      Metric.closedBall 0 r).Finite := by
  apply ((bounded_relative_units_finite ι hι r).image (relativeDifferenceLog ι)).subset
  rintro x ⟨⟨u, rfl⟩, hu⟩
  exact ⟨u, (mem_closedBall_zero_iff.mp hu), rfl⟩

/-- Discreteness comes from arithmetic bounded-conjugate finiteness. -/
theorem differenceLattice_discrete (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    DiscreteTopology (differenceLattice ι) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ (by norm_num)
  · refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.val_injective)
    convert! differenceLattice_inter_ball_finite ι hι 1
    ext x
    refine ⟨?_, fun ⟨hx, hb⟩ ↦ ⟨⟨x, hx⟩, hb, rfl⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact ⟨x.prop, hx⟩

/-- The kernel of the actual relative difference map is finite. -/
theorem relativeDifferenceLog_ker_finite (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Finite (relativeDifferenceLog ι).toIntLinearMap.ker := by
  let f : (relativeDifferenceLog ι).toIntLinearMap.ker → torsion K := fun x ↦
    ⟨x.val.toMul.val, (relativeDifferenceLog_eq_zero_iff ι hι x.val).mp x.prop⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : torsion K ↦ (z : (𝓞 K)ˣ)) h

/-- The ordinary relative lattice has rank exactly the number of complex base places. -/
theorem differenceLattice_rank (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Module.finrank ℤ (differenceLattice ι) = nrComplexPlaces F := by
  letI := relativeDifferenceLog_ker_finite ι hι
  have hz : Module.finrank ℤ (relativeDifferenceLog ι).toIntLinearMap.ker = 0 := by
    apply Module.finrank_eq_zero_iff_isTorsion.mpr
    exact AddMonoid.isTorsion_iff_isTorsion_int.mp is_add_torsion_of_finite
  have h := (relativeDifferenceLog ι).toIntLinearMap.ker.finrank_quotient_add_finrank
  rw [(relativeDifferenceLog ι).toIntLinearMap.quotKerEquivRange.finrank_eq,
    hz, add_zero, normOneUnits_rank_eq_complex_places] at h
  exact h

/-- The actual difference lattice is full, by Dirichlet rank and the finite
Kronecker kernel, with real/integer ranks compared using discreteness. -/
theorem differenceLattice_isZLattice (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    [DiscreteTopology (differenceLattice ι)] :
    IsZLattice ℝ (differenceLattice ι) := by
  constructor
  apply Submodule.eq_top_of_finrank_eq
  have hd : DiscreteTopology (Submodule.span ℤ
      (differenceLattice ι : Set ({w : InfinitePlace F // IsComplex w} → ℝ))) := by
    rw [Submodule.span_eq]
    infer_instance
  have hr := Real.finrank_eq_int_finrank_of_discrete hd
  rw [Set.finrank, Set.finrank, Submodule.span_eq, differenceLattice_rank ι hι] at hr
  simpa only [Module.finrank_fintype_fun_eq_card] using hr

/-- The paper's relative regulator, independently defined as an ordinary
Lebesgue covolume in the actual unweighted difference coordinates. -/
def relativeRegulator (ι : K ≃ₐ[F] K) : ℝ := ZLattice.covolume (differenceLattice ι)

theorem relativeRegulator_pos (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    0 < relativeRegulator ι := by
  letI := differenceLattice_discrete ι hι
  letI := differenceLattice_isZLattice ι hι
  exact ZLattice.covolume_pos (differenceLattice ι) MeasureTheory.volume

/-- The zero-dimensional convention `R_U = 1` is a theorem of the ordinary
covolume definition. -/
theorem relativeRegulator_eq_one_of_no_complex_places (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hc : nrComplexPlaces F = 0) : relativeRegulator ι = 1 := by
  letI := differenceLattice_discrete ι hι
  letI := differenceLattice_isZLattice ι hι
  letI : IsEmpty {w : InfinitePlace F // IsComplex w} := Fintype.card_eq_zero_iff.mp hc
  rw [relativeRegulator, ZLattice.covolume_eq_det _ (IsZLattice.basis (differenceLattice ι))]
  simp

end UnitDistance.RelativeUnits
