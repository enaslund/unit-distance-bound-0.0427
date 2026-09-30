module

public import UnitDistance.RelativeUnitsRegulatorPairs

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual full unit lattice in kernel-and-norm coordinates

The coordinate change is a relabeling followed by `(x,y) ↦ (x,x+y)`
at every complex base place. Its covolume is the ordinary regulator of `K`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace NumberField.Units
open MeasureTheory

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

/-- The actual coordinate change into a first-place block and a norm block. -/
def pairedNormCoordinates (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w}) :
    ({w : InfinitePlace K // w ≠ chosenPlaceAbove (K := K) v.val} → ℝ) ≃ₗ[ℝ]
      (ComplexPlaceIndex F ⊕ NormCoordinateIndex v.val → ℝ) :=
  (reindexCoordinates (deletedPairedPlaceEquiv ι hι v)).symm.trans
    (coordinateShear (pairCoordinateAddition v.val))

/-- Both parts of the coordinate change preserve ordinary Lebesgue volume. -/
theorem pairedNormCoordinates_measurePreserving (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w}) :
    MeasurePreserving (pairedNormCoordinates ι hι v) volume volume := by
  apply (coordinateShear_measurePreserving (pairCoordinateAddition v.val)).comp
  exact (reindexCoordinates_measurePreserving (deletedPairedPlaceEquiv ι hι v)).symm
    (reindexCoordinates (deletedPairedPlaceEquiv ι hι v)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

/-- The actual unit logarithm in first-place and weighted norm coordinates. -/
def pairedUnitLog (v : InfinitePlace F) :
    Additive (𝓞 K)ˣ →+ (ComplexPlaceIndex F ⊕ NormCoordinateIndex v → ℝ) where
  toFun u := Sum.elim
    (fun w ↦ (2 : ℝ) * Real.log (chosenPlaceAbove (K := K) w.val u.toMul))
    (deletedUnitLog F v ((unitNorm (F := F)).toAdditive u))
  map_zero' := by ext (w | w) <;> simp
  map_add' u t := by
    ext (w | w)
    · simp only [Sum.elim_inl, Pi.add_apply, toMul_add, Units.coe_mul, map_mul,
        Real.log_mul (Units.pos_at_place _ _).ne' (Units.pos_at_place _ _).ne']
      ring
    · exact congrFun (map_add ((deletedUnitLog F v).comp (unitNorm (F := F)).toAdditive) u t) w

/-- The geometric coordinate change agrees with the actual arithmetic unit norm. -/
theorem pairedNormCoordinates_deletedUnitLog (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w}) (u : Additive (𝓞 K)ˣ) :
    pairedNormCoordinates ι hι v
      (deletedUnitLog K (chosenPlaceAbove (K := K) v.val) u) = pairedUnitLog v.val u := by
  ext (w | w)
  · change (mult (chosenPlaceAbove (K := K) w.val) : ℝ) *
      Real.log (chosenPlaceAbove (K := K) w.val u.toMul) = _
    rw [IsTotallyComplex.mult_eq]
    rfl
  · by_cases hw : IsReal w.val
    · have h := weighted_log_norm_real ι hι ⟨w.val, hw⟩ u.toMul
      simpa [pairedNormCoordinates, pairedUnitLog, coordinateShear, reindexCoordinates,
        LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', deletedPairedPlaceEquiv,
        pairCoordinateAddition, rawPairedIndex, pairedPlace, deletedUnitLog, hw] using h.symm
    · have h := weighted_log_norm_complex ι hι
        ⟨w.val, not_isReal_iff_isComplex.mp hw⟩ u.toMul
      simpa [pairedNormCoordinates, pairedUnitLog, coordinateShear, reindexCoordinates,
        LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', deletedPairedPlaceEquiv,
        pairCoordinateAddition, rawPairedIndex, pairedPlace, deletedUnitLog, hw, add_comm] using h.symm

/-- The actual full unit lattice, expressed in the two coordinate blocks. -/
abbrev pairedUnitLattice (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w}) :=
  ZLattice.comap ℝ (deletedUnitLattice K (chosenPlaceAbove (K := K) v.val))
    (pairedNormCoordinates ι hι v).symm.toLinearMap

instance pairedUnitLattice_discrete (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w}) : DiscreteTopology (pairedUnitLattice ι hι v) :=
  ZLattice.comap_discreteTopology ℝ (deletedUnitLattice K (chosenPlaceAbove (K := K) v.val))
    (pairedNormCoordinates ι hι v).symm.continuous_of_finiteDimensional
    (pairedNormCoordinates ι hι v).symm.injective

instance pairedUnitLattice_isZLattice (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w}) : IsZLattice ℝ (pairedUnitLattice ι hι v) :=
  instIsZLatticeComap ℝ (deletedUnitLattice K (chosenPlaceAbove (K := K) v.val))
    (pairedNormCoordinates ι hι v).symm.toContinuousLinearEquiv

/-- The coordinate shear and relabeling leave the ordinary regulator unchanged. -/
theorem pairedUnitLattice_covolume (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w}) :
    ZLattice.covolume (pairedUnitLattice ι hι v) = regulator K := by
  rw [← deletedUnitLattice_covolume K (chosenPlaceAbove (K := K) v.val)]
  exact ZLattice.covolume_comap (deletedUnitLattice K (chosenPlaceAbove (K := K) v.val))
    volume volume
    (e := (pairedNormCoordinates ι hι v).symm.toContinuousLinearEquiv)
    ((pairedNormCoordinates_measurePreserving ι hι v).symm
      (pairedNormCoordinates ι hι v).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv)

theorem mem_pairedUnitLattice (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w})
    (x : ComplexPlaceIndex F ⊕ NormCoordinateIndex v.val → ℝ) :
    x ∈ pairedUnitLattice ι hι v ↔
      ∃ u : Additive (𝓞 K)ˣ, pairedUnitLog v.val u = x := by
  change (pairedNormCoordinates ι hι v).symm x ∈
    deletedUnitLattice K (chosenPlaceAbove (K := K) v.val) ↔ _
  rw [mem_deletedUnitLattice]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [← pairedNormCoordinates_deletedUnitLog ι hι v u, hu, LinearEquiv.apply_symm_apply]
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    rw [← pairedNormCoordinates_deletedUnitLog ι hι v u, LinearEquiv.symm_apply_apply]

end UnitDistance.RelativeUnits
