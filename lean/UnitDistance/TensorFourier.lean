module

public import UnitDistance.WitnessFourierConstants
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
set_option backward.privateInPublic true


/-!
# Fourier factorization of the actual Gaussian–Student tensor

Coordinates consist of finitely many singleton complex places and paired
complex places. The measures below are ordinary product Lebesgue measures.
An orthogonal, volume-preserving coordinate equivalence transfers every
statement to the actual Euclidean domain used by Poisson summation.
-/

open MeasureTheory FourierTransform
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Witness

variable {β γ : Type*} [Fintype β] [Fintype γ]

abbrev TensorCoordinates (β γ : Type*) := (β → ℂ) × (γ → ℂ × ℂ)

/-- The literal tensor of the published p-th powers. -/
noncomputable def tensorWeight (x : TensorCoordinates β γ) : ℝ :=
  (∏ i, compactProfile (x.1 i)^p) * (∏ j, pairProfile (x.2 j)^p)

/-- The sum of all ordinary complex-coordinate norms. -/
noncomputable def tensorCoordinateNorm (ξ : TensorCoordinates β γ) : ℝ :=
  (∑ i, ‖ξ.1 i‖) + ∑ j, (‖(ξ.2 j).1‖+‖(ξ.2 j).2‖)

/-- The Euclidean real inner product written in singleton/pair coordinates. -/
noncomputable def tensorInner (x ξ : TensorCoordinates β γ) : ℝ :=
  (∑ i, inner ℝ (x.1 i) (ξ.1 i)) +
    ∑ j, (inner ℝ (x.2 j).1 (ξ.2 j).1 + inner ℝ (x.2 j).2 (ξ.2 j).2)

theorem tensorWeight_pos (x : TensorCoordinates β γ) : 0 < tensorWeight x := by
  apply mul_pos <;> apply Finset.prod_pos <;> intro i _
  · exact Real.rpow_pos_of_pos (Real.exp_pos _) p
  · exact Real.rpow_pos_of_pos (pairProfile_pos _) p

theorem integrable_tensorWeight : Integrable (tensorWeight (β := β) (γ := γ)) := by
  exact (Integrable.fintype_prod (fun _ : β => compactMass_integrable)).mul_prod
    (Integrable.fintype_prod (fun _ : γ => integrable_pairMass))

theorem integral_tensorWeight :
    (∫ x : TensorCoordinates β γ, tensorWeight x) =
      compactMass ^ Fintype.card β * pairMass ^ Fintype.card γ := by
  unfold tensorWeight
  rw [Measure.volume_eq_prod]
  rw [integral_prod_mul (μ := volume) (ν := volume) (fun x : β → ℂ => ∏ i, compactProfile (x i)^p)
    (fun y : γ → ℂ × ℂ => ∏ j, pairProfile (y j)^p)]
  rw [integral_fintype_prod_volume_eq_prod (fun _ : β => fun z : ℂ => compactProfile z^p),
    integral_fintype_prod_volume_eq_prod (fun _ : γ => fun z : ℂ × ℂ => pairProfile z^p)]
  simp only [compactMass, pairMass, Finset.prod_const, Finset.card_univ]

private theorem temperateGrowth_finset_prod {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]
             exact Function.HasTemperateGrowth.const (E := E) (1 : ℝ)
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem temperateGrowth_tensorWeight :
    (tensorWeight (β := β) (γ := γ)).HasTemperateGrowth := by
  have hc (i : β) : (fun x : TensorCoordinates β γ => compactProfile (x.1 i)^p).HasTemperateGrowth :=
    temperateGrowth_compactProfile_rpow.comp
      (((ContinuousLinearMap.proj i : (β → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.fst ℝ (β → ℂ) (γ → ℂ × ℂ))).hasTemperateGrowth)
  have hp (j : γ) : (fun x : TensorCoordinates β γ => pairProfile (x.2 j)^p).HasTemperateGrowth :=
    (temperateGrowth_pairProfile_rpow p).comp
      (((ContinuousLinearMap.proj j : (γ → ℂ × ℂ) →L[ℝ] (ℂ × ℂ)).comp
        (ContinuousLinearMap.snd ℝ (β → ℂ) (γ → ℂ × ℂ))).hasTemperateGrowth)
  exact (temperateGrowth_finset_prod Finset.univ _ (fun i _ => hc i)).mul
    (temperateGrowth_finset_prod Finset.univ _ (fun j _ => hp j))

private theorem exp_sum_kernel {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    Complex.exp (((-2*Real.pi*∑ i, f i:ℝ):ℂ)*Complex.I) =
      ∏ i, Complex.exp (((-2*Real.pi*f i:ℝ):ℂ)*Complex.I) := by
  rw [← Complex.exp_sum]
  congr 1
  simp only [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]

private theorem pairProfile_fourier_integral (ξ : ℂ × ℂ) :
    (∫ x : ℂ × ℂ,
      Complex.exp (((-2*Real.pi*(inner ℝ x.1 ξ.1 + inner ℝ x.2 ξ.2):ℝ):ℂ)*Complex.I) *
        ((pairProfile x^p:ℝ):ℂ)) =
      𝓕 (fun x : WithLp 2 (ℂ × ℂ) => ((pairProfile (WithLp.ofLp x)^p:ℝ):ℂ))
        (WithLp.toLp 2 ξ) := by
  rw [Real.fourier_eq', ← (WithLp.volume_preserving_ofLp ℂ ℂ).integral_comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).toHomeomorph.measurableEmbedding]
  rfl

/-- Fubini factors the literal tensor Fourier integral into its actual block
Fourier transforms. No envelope or independence assumption is used. -/
theorem tensor_fourier_integral (ξ : TensorCoordinates β γ) :
    (∫ x : TensorCoordinates β γ,
      Complex.exp (((-2*Real.pi*tensorInner x ξ:ℝ):ℂ)*Complex.I) * ((tensorWeight x:ℝ):ℂ)) =
      (∏ i, 𝓕 (fun z : ℂ => ((compactProfile z^p:ℝ):ℂ)) (ξ.1 i)) *
      ∏ j, 𝓕 (fun z : WithLp 2 (ℂ × ℂ) => ((pairProfile (WithLp.ofLp z)^p:ℝ):ℂ))
        (WithLp.toLp 2 (ξ.2 j)) := by
  have hkernel (x : TensorCoordinates β γ) :
      Complex.exp (((-2*Real.pi*tensorInner x ξ:ℝ):ℂ)*Complex.I) * ((tensorWeight x:ℝ):ℂ) =
      (∏ i, Complex.exp (((-2*Real.pi*inner ℝ (x.1 i) (ξ.1 i):ℝ):ℂ)*Complex.I) *
        ((compactProfile (x.1 i)^p:ℝ):ℂ)) *
      ∏ j, Complex.exp (((-2*Real.pi*(inner ℝ (x.2 j).1 (ξ.2 j).1 +
        inner ℝ (x.2 j).2 (ξ.2 j).2):ℝ):ℂ)*Complex.I) * ((pairProfile (x.2 j)^p:ℝ):ℂ) := by
    rw [tensorInner, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add,
      exp_sum_kernel, exp_sum_kernel]
    simp only [tensorWeight, Complex.ofReal_mul, Complex.ofReal_prod, Finset.prod_mul_distrib]
    ring
  simp_rw [hkernel]
  rw [Measure.volume_eq_prod]
  rw [integral_prod_mul (μ := volume) (ν := volume)
    (fun x : β → ℂ => ∏ i, Complex.exp (((-2*Real.pi*inner ℝ (x i) (ξ.1 i):ℝ):ℂ)*Complex.I) *
      ((compactProfile (x i)^p:ℝ):ℂ))
    (fun x : γ → ℂ × ℂ => ∏ j, Complex.exp (((-2*Real.pi*(inner ℝ (x j).1 (ξ.2 j).1 +
      inner ℝ (x j).2 (ξ.2 j).2):ℝ):ℂ)*Complex.I) * ((pairProfile (x j)^p:ℝ):ℂ)),
    integral_fintype_prod_volume_eq_prod (fun i : β => fun z : ℂ =>
      Complex.exp (((-2*Real.pi*inner ℝ z (ξ.1 i):ℝ):ℂ)*Complex.I) * ((compactProfile z^p:ℝ):ℂ)),
    integral_fintype_prod_volume_eq_prod (fun j : γ => fun z : ℂ × ℂ =>
      Complex.exp (((-2*Real.pi*(inner ℝ z.1 (ξ.2 j).1 + inner ℝ z.2 (ξ.2 j).2):ℝ):ℂ)*Complex.I) *
        ((pairProfile z^p:ℝ):ℂ))]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Real.fourier_eq']
    rfl
  · exact Finset.prod_congr rfl (fun j _ => pairProfile_fourier_integral (ξ.2 j))

theorem tensor_fourier_integral_envelope (ξ : TensorCoordinates β γ) :
    ‖∫ x : TensorCoordinates β γ,
      Complex.exp (((-2*Real.pi*tensorInner x ξ:ℝ):ℂ)*Complex.I) * ((tensorWeight x:ℝ):ℂ)‖ ≤
      (compactMass ^ Fintype.card β * pairMass ^ Fintype.card γ) *
        2^(Fintype.card β + 2*Fintype.card γ) * Real.exp (-tensorCoordinateNorm ξ) := by
  rw [tensor_fourier_integral, norm_mul, norm_prod, norm_prod]
  have hc : (∏ i, ‖𝓕 (fun z : ℂ => ((compactProfile z^p:ℝ):ℂ)) (ξ.1 i)‖) ≤
      ∏ i, (2*compactMass)*Real.exp (-‖ξ.1 i‖) :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => compactProfile_fourier_envelope_one _)
  have hp : (∏ j, ‖𝓕 (fun z : WithLp 2 (ℂ × ℂ) => ((pairProfile (WithLp.ofLp z)^p:ℝ):ℂ))
      (WithLp.toLp 2 (ξ.2 j))‖) ≤
      ∏ j, (4*pairMass)*Real.exp (-(‖(ξ.2 j).1‖+‖(ξ.2 j).2‖)) :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => pairProfile_fourier_envelope_one _)
  refine (mul_le_mul hc hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    (Finset.prod_nonneg (fun _ _ => by positivity [compactMass_pos]))).trans_eq ?_
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul, pow_add]
  have hcoord : -tensorCoordinateNorm ξ =
      -(∑ i, ‖ξ.1 i‖) + -(∑ j, (‖(ξ.2 j).1‖+‖(ξ.2 j).2‖)) := by
    unfold tensorCoordinateNorm
    ring
  rw [hcoord, Real.exp_add]
  simp only [Finset.sum_neg_distrib]
  ring

section EuclideanDomain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The original tensor in actual Euclidean coordinates. -/
noncomputable def tensorProfile (e : V ≃L[ℝ] TensorCoordinates β γ) (x : V) : ℝ :=
  tensorWeight (e x)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem temperateGrowth_tensorProfile (e : V ≃L[ℝ] TensorCoordinates β γ) :
    (tensorProfile e).HasTemperateGrowth :=
  temperateGrowth_tensorWeight.comp e.hasTemperateGrowth

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem tensorProfile_pos (e : V ≃L[ℝ] TensorCoordinates β γ) (x : V) :
    0 < tensorProfile e x := tensorWeight_pos _

theorem integrable_tensorProfile (e : V ≃L[ℝ] TensorCoordinates β γ)
    (he : MeasurePreserving e volume volume) : Integrable (tensorProfile e) :=
  (he.integrable_comp integrable_tensorWeight.aestronglyMeasurable).mpr integrable_tensorWeight

theorem integral_tensorProfile (e : V ≃L[ℝ] TensorCoordinates β γ)
    (he : MeasurePreserving e volume volume) :
    (∫ x, tensorProfile e x) = compactMass ^ Fintype.card β * pairMass ^ Fintype.card γ := by
  unfold tensorProfile
  rw [he.integral_comp e.toHomeomorph.measurableEmbedding, integral_tensorWeight]

/-- The exact block envelope transported to an ordinary Euclidean space. -/
theorem tensorProfile_fourier_envelope (e : V ≃L[ℝ] TensorCoordinates β γ)
    (he : MeasurePreserving e volume volume)
    (hi : ∀ x ξ, inner ℝ x ξ = tensorInner (e x) (e ξ)) (ξ : V) :
    ‖𝓕 (fun x => ((tensorProfile e x:ℝ):ℂ)) ξ‖ ≤
      (compactMass ^ Fintype.card β * pairMass ^ Fintype.card γ) *
        2^(Fintype.card β + 2*Fintype.card γ) * Real.exp (-tensorCoordinateNorm (e ξ)) := by
  rw [Real.fourier_eq']
  simp_rw [hi, tensorProfile, smul_eq_mul]
  rw [he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x => Complex.exp (((-2*Real.pi*tensorInner x (e ξ):ℝ):ℂ)*Complex.I) * ((tensorWeight x:ℝ):ℂ))]
  exact tensor_fourier_integral_envelope _

end EuclideanDomain
end UnitDistance.Witness
