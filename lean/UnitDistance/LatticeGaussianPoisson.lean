module

public import UnitDistance.LatticeFourierEnvelope
public import UnitDistance.FourierGaussianRegularization

@[expose] public section
set_option backward.privateInPublic true


/-!
# Poisson counting from an original Fourier envelope

An original exponential envelope and its strictly small actual lattice sum
imply the tail bound for the constructed Gaussian regularizations. Both
the vanishing Gaussian loss and the actual regularized masses are used;
no approximation or eventual Fourier-tail hypothesis remains.
-/
noncomputable section
open MeasureTheory Filter DedekindZeta.PoissonSummation
open scoped Classical FourierTransform Topology
namespace UnitDistance
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem gaussianRegularization_tail_eventually_of_envelope
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (q : Seminorm ℝ V) {B : ℝ} (hq : ∀ y, q y ≤ B*‖y‖)
    {f : V → ℝ} (hf : f.HasTemperateGrowth) (hpos : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hbound : ∀ ξ, ‖𝓕 (fun x : V => (f x : ℂ)) ξ‖ ≤ C*Real.exp (-σ*q ξ))
    (hsum : Summable (fun w : {w : dualLattice L // w ≠ 0} =>
      Real.exp (-σ*q (w.1 : V))))
    (hsmall : C*(∑' w : {w : dualLattice L // w ≠ 0}, Real.exp (-σ*q (w.1 : V))) <
      ∫ x, f x) :
    ∀ᶠ n in atTop, nonzeroFourierMass L (gaussianRegularization f n) ≤
      ∫ x, (gaussianRegularization f n x).re := by
  let T := ∑' w : {w : dualLattice L // w ≠ 0}, Real.exp (-σ*q (w.1 : V))
  let m := fun n : ℕ =>
    gaussianExponentialMoment V ((σ*B)*fourierGaussianScale (1/((n:ℝ)+1)))
  have hm : Tendsto m atTop (𝓝 1) := by
    have ht := fourierGaussianKernel_moment_tendsto (V := V) (σ*B)
    have he (n : ℕ) : (∫ y : V, fourierGaussianKernel (1/((n:ℝ)+1)) y *
        Real.exp ((σ*B)*‖y‖)) = m n :=
      integral_fourierGaussianKernel_moment (V := V) (ε := 1/((n:ℝ)+1))
        (by positivity) (σ*B)
    simpa only [he] using ht
  have hleft : Tendsto (fun n => m n*C*T) atTop (𝓝 (C*T)) := by
    simpa only [one_mul] using (hm.mul_const C).mul_const T
  have hright := gaussianRegularization_integral_tendsto volume hf hpos hfi
  have hev := hleft.eventually_lt hright hsmall
  filter_upwards [hev] with n hn
  apply le_trans ?_ hn.le
  have hb : ∀ ξ, ‖𝓕 (gaussianRegularization f n : V → ℂ) ξ‖ ≤
      (m n*C)*Real.exp (-σ*q ξ) := by
    intro ξ
    have ht := gaussianRegularization_seminorm_fourier_envelope q hq hf hfi hC hσ hbound n ξ
    calc
      _ ≤ C*Real.exp (-σ*q ξ)*m n := ht
      _ = (m n*C)*Real.exp (-σ*q ξ) := by ring
  exact nonzeroFourierMass_le_of_summable_envelope L (gaussianRegularization f n)
    (fun ξ => Real.exp (-σ*q ξ)) (m n*C) hsum hb

/-- Uniform translated finite lattice counts from the original profile's
Fourier envelope. Every regularization obligation is proved in this theorem. -/
theorem translated_gaussian_limit_sum_le_of_envelope
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (q : Seminorm ℝ V) {B : ℝ} (hq : ∀ y, q y ≤ B*‖y‖)
    {f : V → ℝ} (hf : f.HasTemperateGrowth) (hpos : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hbound : ∀ ξ, ‖𝓕 (fun x : V => (f x : ℂ)) ξ‖ ≤ C*Real.exp (-σ*q ξ))
    (hsum : Summable (fun w : {w : dualLattice L // w ≠ 0} =>
      Real.exp (-σ*q (w.1 : V))))
    (hsmall : C*(∑' w : {w : dualLattice L // w ≠ 0}, Real.exp (-σ*q (w.1 : V))) <
      ∫ x, f x)
    (r : V) (points : Finset L) :
    ∑ v ∈ points, f (r+v) ≤ 2*(∫ x, f x) / ZLattice.covolume L :=
  gaussian_regularization_poisson_bound L hf hpos hfi
    (gaussianRegularization_tail_eventually_of_envelope L q hq hf hpos hfi hC hσ
      hbound hsum hsmall) r points

end UnitDistance
