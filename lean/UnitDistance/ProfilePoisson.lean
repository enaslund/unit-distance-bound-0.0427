module

public import UnitDistance.PoissonBound
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
set_option backward.privateInPublic true


/-!
# Poisson bounds for the same supported profile under coordinate changes

The limiting weight is exactly the supported exponential of the base energy
composed with the stated measure-preserving coordinates. Its mass is proved
to equal the base supported integral. In particular neither an unrelated
energy nor an unrelated mass can be substituted in this interface.
-/

open MeasureTheory Filter
open scoped Classical Topology

namespace UnitDistance

noncomputable def supportedWeight {X : Type*} (S : Set X) (E : X → ℝ) (p : ℝ) : X → ℝ :=
  S.indicator (fun x => Real.exp (-p*E x))

theorem supportedWeight_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (hS : MeasurableSet S) (E : X → ℝ) (p : ℝ) :
    (∫ x, supportedWeight S E p x ∂μ) = ∫ x in S, Real.exp (-p*E x) ∂μ :=
  integral_indicator hS

theorem transformed_supportedWeight_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (hS : MeasurableSet S) (E : X → ℝ) (p : ℝ)
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) :
    (∫ x, supportedWeight S E p (e x) ∂μ) = ∫ x in S, Real.exp (-p*E x) ∂μ := by
  rw [he.integral_comp' (supportedWeight S E p), supportedWeight_integral μ S hS E p]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Explicit profile and covolume version of the finite Poisson limit bound.
The hypotheses concern actual approximating integrals, actual dual Fourier
tails and pointwise convergence to the same transformed supported profile.
The conclusion is uniform in every translate and every finite subset of
lattice points lying in the transformed support. -/
theorem profile_poisson_weighted_sum_le
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (S : Set V) (hS : MeasurableSet S) (E : V → ℝ) (p : ℝ)
    (e : V ≃ᵐ V) (he : MeasurePreserving e volume volume)
    (f : ℕ → SchwartzMap V ℂ) (Aseq : ℕ → ℝ)
    (hAseq : ∀ n, 0 ≤ Aseq n)
    (hIntegral : ∀ n, (∫ x, (f n : V → ℂ) x) = (Aseq n : ℂ))
    (hf : ∀ n x, 0 ≤ ((f n : V → ℂ) x).re)
    (hTail : ∀ n, nonzeroFourierMass L (f n) ≤ Aseq n)
    (hMass : Tendsto Aseq atTop (𝓝 (∫ x, supportedWeight S E p (e x))))
    (hPointwise : ∀ x, Tendsto (fun n => ((f n : V → ℂ) x).re)
      atTop (𝓝 (supportedWeight S E p (e x))))
    (r : V) (points : Finset L) (hSupport : ∀ v ∈ points, e (r+v) ∈ S) :
    ∑ v ∈ points, Real.exp (-p*E (e (r+v))) ≤
      2*(∫ x in S, Real.exp (-p*E x)) / ZLattice.covolume L := by
  have hbound := translated_limit_weighted_sum_le L f Aseq
    (∫ x, supportedWeight S E p (e x)) (fun x => supportedWeight S E p (e x))
    hAseq hIntegral hf hTail hMass hPointwise r points
  rw [transformed_supportedWeight_integral volume S hS E p e he] at hbound
  have hsum : (∑ v ∈ points, supportedWeight S E p (e (r+v))) =
      ∑ v ∈ points, Real.exp (-p*E (e (r+v))) := by
    apply Finset.sum_congr rfl
    intro v hv
    exact Set.indicator_of_mem (hSupport v hv) _
  rwa [hsum] at hbound

end UnitDistance
