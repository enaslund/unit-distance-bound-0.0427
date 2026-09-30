module

public import UnitDistance.PoissonBound

@[expose] public section
set_option backward.privateInPublic true


/-! Bounding an actual lattice Fourier tail by a summable envelope. -/
noncomputable section
open MeasureTheory Filter DedekindZeta.PoissonSummation
open scoped Classical FourierTransform Topology
namespace UnitDistance
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Sum a pointwise envelope on the actual nonzero dual lattice. -/
theorem nonzeroFourierMass_le_of_summable_envelope
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : SchwartzMap V ℂ) (g : V → ℝ) (C : ℝ)
    (hg : Summable (fun w : {w : dualLattice L // w ≠ 0} => g (w.1 : V)))
    (hbound : ∀ ξ, ‖𝓕 (f : V → ℂ) ξ‖ ≤ C*g ξ) :
    nonzeroFourierMass L f ≤ C*∑' w : {w : dualLattice L // w ≠ 0}, g (w.1 : V) := by
  have hs := (summable_fourier_norm L f).subtype (fun w => w ≠ 0)
  have ht : (∑' w : {w : dualLattice L // w ≠ 0}, ‖𝓕 (f : V → ℂ) (w.1 : V)‖) ≤
      ∑' w : {w : dualLattice L // w ≠ 0}, C*g (w.1 : V) :=
    Summable.tsum_le_tsum (fun w => hbound (w.1 : V)) hs (hg.mul_left C)
  rw [tsum_mul_left] at ht
  exact ht

end UnitDistance
