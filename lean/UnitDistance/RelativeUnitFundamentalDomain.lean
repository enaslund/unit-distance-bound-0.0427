module

public import UnitDistance.RelativeUnitEnumeration
public import UnitDistance.GeometryUnfolding
public import UnitDistance.GeometryLogSupport

@[expose] public section
set_option backward.privateInPublic true


/-! The actual relative-unit logarithmic lattice has a bounded measurable
fundamental domain of volume R_U, supplying the domain used by unfolding. -/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped Classical ENNReal
namespace UnitDistance.RelativeUnits
variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

def relativeLogBasis (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Module.Basis {w : InfinitePlace F // IsComplex w} ℝ
      ({w : InfinitePlace F // IsComplex w} → ℝ) := by
  letI := differenceLattice_discrete ι hι
  letI := differenceLattice_isZLattice ι hι
  exact (IsZLattice.basis (differenceLattice ι)).ofZLatticeBasis ℝ

def relativeLogDomain (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Set ({w : InfinitePlace F // IsComplex w} → ℝ) :=
  ZSpan.fundamentalDomain (relativeLogBasis ι hι)

theorem relativeLogDomain_fundamental (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    IsAddFundamentalDomain (differenceLattice ι) (relativeLogDomain ι hι) volume := by
  letI := differenceLattice_discrete ι hι
  letI := differenceLattice_isZLattice ι hι
  exact ZLattice.isAddFundamentalDomain (IsZLattice.basis (differenceLattice ι)) volume

theorem relativeLogDomain_measurable (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    MeasurableSet (relativeLogDomain ι hι) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem relativeLogDomain_bounded (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Bornology.IsBounded (relativeLogDomain ι hι) :=
  ZSpan.fundamentalDomain_isBounded _

theorem relativeLogDomain_finite (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    volume (relativeLogDomain ι hι) < ⊤ :=
  (relativeLogDomain_bounded ι hι).measure_lt_top

theorem relativeLogDomain_volumeReal (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    (volume (relativeLogDomain ι hι)).toReal = relativeRegulator ι := by
  letI := differenceLattice_discrete ι hι
  letI := differenceLattice_isZLattice ι hι
  exact (ZLattice.covolume_eq_measure_fundamentalDomain (differenceLattice ι) volume
    (relativeLogDomain_fundamental ι hι)).symm

theorem relativeLogDomain_volume (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    volume (relativeLogDomain ι hι) = ENNReal.ofReal (relativeRegulator ι) := by
  rw [← relativeLogDomain_volumeReal ι hι,
    ENNReal.ofReal_toReal (relativeLogDomain_finite ι hι).ne]

theorem relativeLogDomain_positive (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    volume (relativeLogDomain ι hι) ≠ 0 := by
  rw [relativeLogDomain_volume]
  exact (ENNReal.ofReal_pos.mpr (relativeRegulator_pos ι hι)).ne'

/-- The half-open domain has an explicit compact parallelepiped enclosure. -/
theorem relativeLogDomain_compact_enclosure (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    ∃ Qbar : Set ({w : InfinitePlace F // IsComplex w} → ℝ),
      relativeLogDomain ι hι ⊆ Qbar ∧ IsCompact Qbar := by
  refine ⟨(relativeLogBasis ι hι).parallelepiped, ?_,
    (relativeLogBasis ι hι).parallelepiped.isCompact⟩
  rw [Module.Basis.coe_parallelepiped]
  exact ZSpan.fundamentalDomain_subset_parallelepiped _

/-- Compact overlap supports admit one finite cutoff on the actual relative
unit-log lattice for all labels and all parameters in its actual domain. -/
theorem relativeLogDomain_finite_cutoff (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    {I J : Type*} [Fintype I] [Fintype J]
    (Φ : J → ({w : InfinitePlace F // IsComplex w} → ℝ) → ℝ≥0∞)
    (hΦ : ∀ j, HasCompactSupport (Φ j))
    (shift : I → J → ({w : InfinitePlace F // IsComplex w} → ℝ)) :
    ∃ cutoff : Finset (differenceLattice ι),
      ∀ i j h, h ∈ relativeLogDomain ι hι → ∀ l ∉ cutoff,
        Φ j (shift i j-((l : ({w : InfinitePlace F // IsComplex w} → ℝ))+h)) = 0 := by
  letI := differenceLattice_discrete ι hι
  letI := differenceLattice_isZLattice ι hι
  obtain ⟨Qbar, hQ, hcompact⟩ := relativeLogDomain_compact_enclosure ι hι
  exact finite_log_cutoff_of_compactSupport (differenceLattice ι).toAddSubgroup
    AddSubgroup.isClosed_of_discrete _ Qbar hQ hcompact Φ hΦ shift

end UnitDistance.RelativeUnits
