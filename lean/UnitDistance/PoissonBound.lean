module

public import UnitDistance.ThirdParty.PoissonSummation

@[expose] public section
set_option backward.privateInPublic true


/-!
# Uniform translated-lattice bounds from the actual dual Fourier tail

The Poisson identity is imported from the credited `sum_product` adaptation.
This module proves a pointwise weighted lattice estimate from a bound on an
independently defined Fourier tail. It does not assume the lattice point sum.
All integrals use the canonical inner-product-space Lebesgue measure, exactly
as in the Fourier transform and `ZLattice.covolume`.
-/

open MeasureTheory
open Filter
open scoped Classical FourierTransform RealInnerProductSpace Topology
open DedekindZeta.PoissonSummation

namespace UnitDistance

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The dual of a full-rank lattice is itself full-rank. -/
instance isZLattice_dual (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    IsZLattice ℝ (dualLattice L) := by
  classical
  constructor
  rw [dualLattice_eq_span_dualBasis L]
  exact ZSpan.span_top _

/-- The exact nonzero dual Fourier mass, without a normalization convention
hidden in a certificate or an input flag. -/
noncomputable def nonzeroFourierMass (L : Submodule ℤ V) (f : SchwartzMap V ℂ) : ℝ :=
  ∑' w : {w : dualLattice L // w ≠ 0}, ‖𝓕 (f : V → ℂ) (w.1 : V)‖

/-- Schwartz decay makes the complete Fourier norm sum summable on the
actual dual lattice. -/
theorem summable_fourier_norm (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : SchwartzMap V ℂ) : Summable (fun w : dualLattice L => ‖𝓕 (f : V → ℂ) (w : V)‖) := by
  have hs := (summable_periodisation (dualLattice L) (SchwartzMap.fourierTransformCLM ℂ f) 0).norm
  simpa only [zero_add, SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe] using hs

/-- The zero dual frequency is the ordinary integral, and the rest is the
independently defined nonzero tail. -/
theorem fourier_norm_sum_split (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : SchwartzMap V ℂ) :
    (∑' w : dualLattice L, ‖𝓕 (f : V → ℂ) (w : V)‖) =
      ‖∫ x, (f : V → ℂ) x‖ + nonzeroFourierMass L f := by
  have hs := (summable_fourier_norm L f).sum_add_tsum_compl (s := {0})
  have hz : 𝓕 (f : V → ℂ) 0 = ∫ x, (f : V → ℂ) x := by
    rw [Real.fourier_eq]
    simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  have hset : ((↑({0} : Finset (dualLattice L)) : Set (dualLattice L))ᶜ) =
      {w : dualLattice L | w ≠ 0} := by ext; simp
  rw [hset] at hs
  simp only [Finset.sum_singleton, ZeroMemClass.coe_zero, hz] at hs
  change _ = _ + (∑' w : {w : dualLattice L // w ≠ 0}, ‖𝓕 (f : V → ℂ) (w.1 : V)‖)
  convert hs.symm using 1
  congr 1

/-- Poisson summation and the modulus-one characters give a uniform norm
bound at every additive translate. -/
theorem translated_schwartz_norm_le (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : SchwartzMap V ℂ) (r : V) :
    ‖∑' v : L, (f : V → ℂ) (r + v)‖ ≤
      (‖∫ x, (f : V → ℂ) x‖ + nonzeroFourierMass L f) / ZLattice.covolume L := by
  change ‖periodisation L f r‖ ≤ _
  rw [periodisation_eq_tsum_fourier]
  have hb := norm_tsum_le_tsum_norm (summable_periodisation_fourier L f r).norm
  have hc : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  simp only [Circle.norm_smul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc] at hb
  rw [tsum_mul_left, fourier_norm_sum_split] at hb
  simpa only [div_eq_mul_inv, mul_comm] using hb

/-- A Fourier-tail bound by the zero-frequency mass gives the factor-two
Schwartz weighted bound on every finite subset of every translated lattice.
The finite set is arbitrary and the same translate occurs throughout. -/
theorem translated_schwartz_weighted_sum_le
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : SchwartzMap V ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hIntegral : (∫ x, (f : V → ℂ) x) = (A : ℂ))
    (hf : ∀ x, 0 ≤ ((f : V → ℂ) x).re)
    (hTail : nonzeroFourierMass L f ≤ A) (r : V) (S : Finset L) :
    ∑ v ∈ S, ((f : V → ℂ) (r + v)).re ≤ 2*A / ZLattice.covolume L := by
  have hs := summable_periodisation L f r
  have hsr : Summable (fun v : L => ((f : V → ℂ) (r + v)).re) := (Complex.hasSum_re hs.hasSum).summable
  have hsub : (∑ v ∈ S, ((f : V → ℂ) (r + v)).re) ≤
      (∑' v : L, (f : V → ℂ) (r + v)).re := by
    rw [Complex.re_tsum hs]
    exact hsr.sum_le_tsum S (fun v _ => hf (r + v))
  have hnorm := translated_schwartz_norm_le L f r
  rw [hIntegral, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA] at hnorm
  exact hsub.trans ((Complex.re_le_norm _).trans (hnorm.trans
    (div_le_div_of_nonneg_right (by linarith) (ZLattice.covolume_pos L volume).le)))

/-- A pointwise limit of nonnegative Schwartz weights inherits the finite
lattice estimate when their integrals converge and their actual Fourier
tails satisfy the same bounds. This isolates the analytic obligations of a
Gaussian damping argument without presuming a Poisson formula for a
non-Schwartz limit. No infinite lattice sum is interchanged with a limit. -/
theorem translated_limit_weighted_sum_le
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : ℕ → SchwartzMap V ℂ) (Aseq : ℕ → ℝ) (A : ℝ) (F : V → ℝ)
    (hAseq : ∀ n, 0 ≤ Aseq n)
    (hIntegral : ∀ n, (∫ x, (f n : V → ℂ) x) = (Aseq n : ℂ))
    (hf : ∀ n x, 0 ≤ ((f n : V → ℂ) x).re)
    (hTail : ∀ n, nonzeroFourierMass L (f n) ≤ Aseq n)
    (hA : Tendsto Aseq atTop (𝓝 A))
    (hF : ∀ x, Tendsto (fun n => ((f n : V → ℂ) x).re) atTop (𝓝 (F x)))
    (r : V) (S : Finset L) :
    ∑ v ∈ S, F (r + v) ≤ 2*A / ZLattice.covolume L := by
  have hleft : Tendsto (fun n => ∑ v ∈ S, ((f n : V → ℂ) (r + v)).re)
      atTop (𝓝 (∑ v ∈ S, F (r + v))) :=
    tendsto_finsetSum S (fun v _ => hF (r + v))
  have hright : Tendsto (fun n => 2*Aseq n / ZLattice.covolume L)
      atTop (𝓝 (2*A / ZLattice.covolume L)) :=
    (tendsto_const_nhds.mul hA).div_const _
  exact le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall fun n =>
    translated_schwartz_weighted_sum_le L (f n) (Aseq n) (hAseq n)
      (hIntegral n) (hf n) (hTail n) r S)

/-- Finite-place periodic fibers contribute their actual finite weighted
mass. Each fiber may have a different additive translate and finite subset;
the Fourier-tail estimate is uniform in both. -/
theorem finite_coset_schwartz_bound {C : Type*}
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : SchwartzMap V ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hIntegral : (∫ x, (f : V → ℂ) x) = (A : ℂ))
    (hf : ∀ x, 0 ≤ ((f : V → ℂ) x).re)
    (hTail : nonzeroFourierMass L f ≤ A)
    (cells : Finset C) (weight : C → ℝ) (hw : ∀ c ∈ cells, 0 ≤ weight c)
    (shift : C → V) (points : C → Finset L) :
    ∑ c ∈ cells, weight c * ∑ v ∈ points c, ((f : V → ℂ) (shift c + v)).re ≤
      2*A * (∑ c ∈ cells, weight c) / ZLattice.covolume L := by
  calc
    _ ≤ ∑ c ∈ cells, weight c * (2*A / ZLattice.covolume L) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left
        (translated_schwartz_weighted_sum_le L f A hA hIntegral hf hTail (shift c) (points c))
        (hw c hc)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The covolume change for a finite-place period is exposed as an exact
identity. Consequently the finite Haar mass `cellVolume * ∑ weight` appears
once, with no extra residue-unit factor. The arithmetic realization of the
cells and this covolume identity are separate field-theoretic obligations. -/
theorem finite_period_schwartz_bound {C : Type*}
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : SchwartzMap V ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hIntegral : (∫ x, (f : V → ℂ) x) = (A : ℂ))
    (hf : ∀ x, 0 ≤ ((f : V → ℂ) x).re)
    (hTail : nonzeroFourierMass L f ≤ A)
    (cells : Finset C) (weight : C → ℝ) (hw : ∀ c ∈ cells, 0 ≤ weight c)
    (shift : C → V) (points : C → Finset L)
    (cellVolume D : ℝ)
    (hcovol : ZLattice.covolume L = D / cellVolume) :
    ∑ c ∈ cells, weight c * ∑ v ∈ points c, ((f : V → ℂ) (shift c + v)).re ≤
      2*A * (cellVolume * ∑ c ∈ cells, weight c) / D := by
  have h := finite_coset_schwartz_bound L f A hA hIntegral hf hTail cells weight hw shift points
  rw [hcovol, div_div_eq_mul_div] at h
  convert h using 1
  ring

end UnitDistance
