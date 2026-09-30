module

public import UnitDistance.HeckeParityUnitAverage

@[expose] public section
set_option backward.privateInPublic true


open Complex Set MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real Classical
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis

/-- Finite linearity of the actual Mellin integral, with convergence proved for every term. -/
theorem hasMellin_finsetSum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ) (s : ℂ)
    (hf : ∀ i ∈ S, MellinConvergent (f i) s) :
    HasMellin (fun t => ∑ i ∈ S, f i t) s (∑ i ∈ S, mellin (f i) s) := by
  constructor
  · unfold MellinConvergent
    simp_rw [Finset.smul_sum]
    exact integrable_finsetSum S hf
  · unfold mellin
    simp_rw [Finset.smul_sum]
    exact integral_finsetSum S hf

variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*}

/-- An arbitrary finite combination of actual unit-box parity theta functions,
with independent positive radial scalings for the different lattices. -/
noncomputable def finiteHeckeParityUnitAverage (p : index K → Bool) (S : Finset ι)
    (L : ι → Submodule ℤ (EuclideanSpace ℝ (index K)))
    (coeff : ι → ℂ) (scale : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, coeff i * heckeParityUnitAverage K p (L i) (scale i * t)

theorem mellinConvergent_finiteHeckeParityUnitAverage
    (p : index K → Bool) (hp : ∃ j, p j = true) (S : Finset ι)
    (L : ι → Submodule ℤ (EuclideanSpace ℝ (index K)))
    [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)]
    (coeff : ι → ℂ) (scale : ι → ℝ) (hscale : ∀ i ∈ S, 0 < scale i) (s : ℂ) :
    MellinConvergent (finiteHeckeParityUnitAverage K p S L coeff scale) s := by
  apply (hasMellin_finsetSum S
    (fun i t => coeff i * heckeParityUnitAverage K p (L i) (scale i*t)) s ?_).1
  intro i hi
  have h := (MellinConvergent.comp_mul_left (hscale i hi)).mpr
    (mellinConvergent_heckeParityUnitAverage K p hp (L i) s)
  simpa only [smul_eq_mul] using h.const_smul (coeff i)

theorem mellin_finiteHeckeParityUnitAverage
    (p : index K → Bool) (hp : ∃ j, p j = true) (S : Finset ι)
    (L : ι → Submodule ℤ (EuclideanSpace ℝ (index K)))
    [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)]
    (coeff : ι → ℂ) (scale : ι → ℝ) (hscale : ∀ i ∈ S, 0 < scale i) (s : ℂ) :
    mellin (finiteHeckeParityUnitAverage K p S L coeff scale) s =
      ∑ i ∈ S, coeff i * ((scale i : ℂ)^(-s) * mellin (heckeParityUnitAverage K p (L i)) s) := by
  have hf (i : ι) (hi : i ∈ S) :
      MellinConvergent (fun t => coeff i * heckeParityUnitAverage K p (L i) (scale i*t)) s := by
    have h := (MellinConvergent.comp_mul_left (hscale i hi)).mpr
      (mellinConvergent_heckeParityUnitAverage K p hp (L i) s)
    simpa only [smul_eq_mul] using h.const_smul (coeff i)
  unfold finiteHeckeParityUnitAverage
  rw [(hasMellin_finsetSum S
    (fun i t => coeff i * heckeParityUnitAverage K p (L i) (scale i*t)) s hf).2]
  apply Finset.sum_congr rfl
  intro i hi
  change mellin (fun t => coeff i • heckeParityUnitAverage K p (L i) (scale i*t)) s = _
  rw [mellin_const_smul, mellin_comp_mul_left _ _ (hscale i hi)]
  rfl

/-- Actual entire Mellin transform of every finite dyadic/class combination.
All lattice Poisson estimates and convergence obligations are discharged. -/
theorem differentiable_mellin_finiteHeckeParityUnitAverage
    (p : index K → Bool) (hp : ∃ j, p j = true) (S : Finset ι)
    (L : ι → Submodule ℤ (EuclideanSpace ℝ (index K)))
    [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)]
    (coeff : ι → ℂ) (scale : ι → ℝ) (hscale : ∀ i ∈ S, 0 < scale i) :
    Differentiable ℂ (mellin (finiteHeckeParityUnitAverage K p S L coeff scale)) := by
  have heq : mellin (finiteHeckeParityUnitAverage K p S L coeff scale) =
      fun s => ∑ i ∈ S, coeff i * ((scale i : ℂ)^(-s) * mellin (heckeParityUnitAverage K p (L i)) s) :=
    funext (mellin_finiteHeckeParityUnitAverage K p hp S L coeff scale hscale)
  rw [heq]
  apply Differentiable.fun_sum
  intro i hi
  have hc : Differentiable ℂ (fun s : ℂ => (scale i : ℂ)^(-s)) :=
    differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (hscale i hi).ne'))
  exact (hc.mul (differentiable_mellin_heckeParityUnitAverage K p hp (L i))).const_mul (coeff i)

end UnitDistance.NumberFieldAnalysis
