module

public import UnitDistance.EuclideanIdealDual
public import UnitDistance.MinkowskiFractionalTrace

@[expose] public section
set_option backward.privateInPublic true


/-! Ordinary Euclidean duality for every actual nonzero fractional ideal. -/
noncomputable section
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace DedekindZeta
open scoped nonZeroDivisors Classical RealInnerProductSpace
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K]

/-- The full ordinary Euclidean dual of a nonzero fractional ideal lattice. -/
theorem mem_dual_fractional_lattice_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : Space K) :
    y ∈ PoissonSummation.dualLattice
        (lattice K I) ↔
      ∃ b ∈ (MinkowskiTrace.dualFractionalIdeal K I : Submodule (𝓞 K) K),
        coordinates K y = dualCoordinates K (mixedEmbedding K b) := by
  rw [PoissonSummation.mem_dualLattice]
  have hgen : (∀ x ∈ lattice K I, inner ℝ y x ∈ (1 : Submodule ℤ ℝ)) ↔
      ∀ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K),
        ∃ k : ℤ, MinkowskiTrace.traceForm K (traceCoordinates K (coordinates K y)) a = k := by
    constructor
    · intro h a ha
      obtain ⟨k, hk⟩ := Submodule.mem_one.mp (h (embedding K a)
        ((mem_lattice_iff K _ _).mpr ⟨a, ha, rfl⟩))
      exact ⟨k, by rw [inner_embedding] at hk; simpa using hk.symm⟩
    · intro h x hx
      obtain ⟨a, ha, rfl⟩ := (mem_lattice_iff K _ x).mp hx
      obtain ⟨k, hk⟩ := h a ha
      refine Submodule.mem_one.mpr ⟨k, ?_⟩
      rw [inner_embedding]
      simpa using hk.symm
  rw [hgen, MinkowskiTrace.traceForm_int_iff_exists_dualFractionalIdeal K I I.ne_zero]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  constructor
  · intro h
    rw [h, dual_traceCoordinates]
  · intro h
    rw [h, trace_dualCoordinates]


end UnitDistance.EuclideanIdeal
