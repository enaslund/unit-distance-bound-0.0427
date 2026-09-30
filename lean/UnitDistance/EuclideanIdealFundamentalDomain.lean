module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import UnitDistance.EuclideanIdealDual

@[expose] public section
set_option backward.privateInPublic true


/-!
# An actual additive fundamental domain of the Euclidean ideal lattice

Choose an actual integral basis of the fractional ideal lattice and its
half-open real parallelepiped. The ordinary volume is exactly the proved
ideal covolume, with no unspecified Haar normalization.
-/

noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors Classical ENNReal

namespace UnitDistance.EuclideanIdeal

variable (K : Type*) [Field K] [NumberField K]

/-- An actual real basis obtained from an integral basis of the ideal lattice. -/
def idealRealBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (lattice K I)) ℝ (Space K) :=
  (Module.Free.chooseBasis ℤ (lattice K I)).ofZLatticeBasis ℝ

/-- The literal half-open fundamental parallelepiped of the chosen ideal basis. -/
def idealFundamentalDomain (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Set (Space K) :=
  ZSpan.fundamentalDomain (idealRealBasis K I)

theorem idealFundamentalDomain_fundamental (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsAddFundamentalDomain (lattice K I).toAddSubgroup (idealFundamentalDomain K I) volume :=
  ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (lattice K I)) volume

theorem idealFundamentalDomain_measurable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeasurableSet (idealFundamentalDomain K I) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem idealFundamentalDomain_bounded (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Bornology.IsBounded (idealFundamentalDomain K I) :=
  ZSpan.fundamentalDomain_isBounded _

theorem idealFundamentalDomain_finite (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    volume (idealFundamentalDomain K I) < ⊤ :=
  (idealFundamentalDomain_bounded K I).measure_lt_top

/-- The actual additive translation domain has the ordinary ideal covolume. -/
theorem idealFundamentalDomain_volumeReal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (volume (idealFundamentalDomain K I)).toReal =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)*
        (2⁻¹)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)| := by
  rw [← covolume_lattice K I]
  exact (ZLattice.covolume_eq_measure_fundamentalDomain (lattice K I) volume
    (idealFundamentalDomain_fundamental K I)).symm

theorem idealFundamentalDomain_volume (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    volume (idealFundamentalDomain K I) =
      ENNReal.ofReal ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)*
        (2⁻¹)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  rw [← idealFundamentalDomain_volumeReal K I,
    ENNReal.ofReal_toReal (idealFundamentalDomain_finite K I).ne]

theorem idealFundamentalDomain_positive (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    volume (idealFundamentalDomain K I) ≠ 0 := by
  have hpos : 0 < (volume (idealFundamentalDomain K I)).toReal := by
    rw [idealFundamentalDomain_volumeReal, ← covolume_lattice K I]
    exact ZLattice.covolume_pos (lattice K I) volume
  intro hzero
  rw [hzero, ENNReal.toReal_zero] at hpos
  exact hpos.false

/-- The half-open domain is contained in its actual compact parallelepiped. -/
theorem idealFundamentalDomain_compact_enclosure (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ Pbar : Set (Space K), idealFundamentalDomain K I ⊆ Pbar ∧ IsCompact Pbar := by
  refine ⟨(idealRealBasis K I).parallelepiped, ?_, (idealRealBasis K I).parallelepiped.isCompact⟩
  rw [Module.Basis.coe_parallelepiped]
  exact ZSpan.fundamentalDomain_subset_parallelepiped _

end UnitDistance.EuclideanIdeal
