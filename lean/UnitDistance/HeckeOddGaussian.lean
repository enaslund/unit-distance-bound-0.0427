module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Gaussian kernels with odd real-place factors

Actual Fourier transforms for `x exp(-π a x²)` and its normalized version
`sqrt(a) x exp(-π a x²)`, followed by arbitrary finite products of even and
odd coordinates. The normalized parity kernel obeys a uniform Gaussian
majorant with weights divided by two. If any coordinate is odd, both the
kernel and its Fourier transform vanish at the origin.

These are analytic ingredients for signed Hecke theta functions. They do
not construct a number-field character or identify an L-function.
-/

open Complex MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis

noncomputable def heckeRealGaussian (a x : ℝ) : ℂ :=
  Complex.exp (-Real.pi * (a : ℂ) * (x : ℂ)^2)

noncomputable def heckeOddGaussian (a x : ℝ) : ℂ :=
  (x : ℂ) * heckeRealGaussian a x

theorem heckeRealGaussian_ofReal (a x : ℝ) :
    heckeRealGaussian a x = (Real.exp (-Real.pi*a*x^2) : ℂ) := by
  simp [heckeRealGaussian, Complex.ofReal_exp]

theorem integrable_heckeRealGaussian {a : ℝ} (ha : 0 < a) :
    Integrable (heckeRealGaussian a) := by
  have h : Integrable (fun x : ℝ => (Real.exp (-(Real.pi*a)*x^2) : ℂ)) :=
    (integrable_exp_neg_mul_sq (mul_pos Real.pi_pos ha)).ofReal
  change Integrable (fun x => heckeRealGaussian a x)
  simpa only [heckeRealGaussian_ofReal, neg_mul] using h

theorem integrable_heckeOddGaussian {a : ℝ} (ha : 0 < a) :
    Integrable (heckeOddGaussian a) := by
  have h : Integrable (fun x : ℝ => ((x * Real.exp (-(Real.pi*a)*x^2) : ℝ) : ℂ)) :=
    (integrable_mul_exp_neg_mul_sq (mul_pos Real.pi_pos ha)).ofReal
  change Integrable (fun x => heckeOddGaussian a x)
  simpa only [heckeOddGaussian, heckeRealGaussian_ofReal, Complex.ofReal_mul, neg_mul] using h

theorem fourier_heckeRealGaussian {a : ℝ} (ha : 0 < a) :
    𝓕 (heckeRealGaussian a) = fun t : ℝ =>
      1/(a : ℂ)^(1/2 : ℂ) * Complex.exp (-Real.pi/(a : ℂ)*(t : ℂ)^2) := by
  exact fourier_gaussian_pi ha

theorem fourier_heckeOddGaussian {a : ℝ} (ha : 0 < a) (t : ℝ) :
    𝓕 (heckeOddGaussian a) t =
      -Complex.I * (t : ℂ)/(a : ℂ) *
        (1/(a : ℂ)^(1/2 : ℂ) * Complex.exp (-Real.pi/(a : ℂ)*(t : ℂ)^2)) := by
  have hf' : Integrable (fun x : ℝ => x • heckeRealGaussian a x) := by
    have h := integrable_heckeOddGaussian ha
    unfold heckeOddGaussian at h
    simpa only [Complex.real_smul] using h
  have hf := Real.hasDerivAt_fourier (integrable_heckeRealGaussian ha) hf' t
  rw [fourier_heckeRealGaussian ha] at hf
  have hg := (((Complex.ofRealCLM.hasDerivAt (x := t)).pow 2).const_mul
    (-Real.pi/(a : ℂ))).cexp.const_mul (1/(a : ℂ)^(1/2 : ℂ))
  have heq := hf.unique hg
  have hfun : (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) •
      heckeRealGaussian a x) = (-2 * (Real.pi : ℂ) * Complex.I) • heckeOddGaussian a := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, heckeOddGaussian]
    ring
  have hlin : 𝓕 ((-2 * (Real.pi : ℂ) * Complex.I) • heckeOddGaussian a) t =
      (-2 * (Real.pi : ℂ) * Complex.I) * 𝓕 (heckeOddGaussian a) t := by
    exact congrFun (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume
      (innerₗ ℝ) (heckeOddGaussian a) (-2 * (Real.pi : ℂ) * Complex.I)) t
  rw [hfun, hlin] at heq
  change (-2 * (Real.pi : ℂ) * Complex.I) * 𝓕 (heckeOddGaussian a) t = _ at heq
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hp0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_left_cancel₀ (show -2 * (Real.pi : ℂ) * Complex.I ≠ 0 by simp [hp0])
  rw [heq]
  simp only [Pi.pow_apply, Complex.ofRealCLM_apply, Complex.ofReal_one, Nat.cast_ofNat,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_one]
  field_simp [ha0]
  simp only [Complex.I_sq]
  ring



/-- Fourier transform factors coordinatewise for a tensor product on Euclidean space. -/
theorem fourier_euclidean_product {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (w : EuclideanSpace ℝ ι) :
    𝓕 (fun x : EuclideanSpace ℝ ι => ∏ i, f i (x i)) w =
      ∏ i, 𝓕 (f i) (w i) := by
  rw [Real.fourier_eq']
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  have hker (x : ι → ℝ) :
      Complex.exp (((-2 * Real.pi * inner ℝ (WithLp.toLp 2 x) w : ℝ) : ℂ) * Complex.I) =
        ∏ i, Complex.exp (((-2 * Real.pi * x i * w i : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      ← Finset.mul_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, mul_assoc]
    congr 3
    congr 1
    exact Finset.sum_congr rfl (fun i _ => mul_comm (w i) (x i))
  simp_rw [hker, smul_eq_mul, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod (f := fun i x =>
    Complex.exp (((-2 * Real.pi * x * w i : ℝ) : ℂ) * Complex.I) * f i x)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.fourier_real_eq_integral_exp_smul]
  rfl

/-- Independent even/odd choices at each real Euclidean coordinate. -/
noncomputable def heckeParityGaussian {ι : Type*} [Fintype ι]
    (p : ι → Bool) (a : ι → ℝ) (x : EuclideanSpace ℝ ι) : ℂ :=
  ∏ i, if p i then heckeOddGaussian (a i) (x i) else heckeRealGaussian (a i) (x i)

theorem fourier_heckeParityGaussian {ι : Type*} [Fintype ι]
    (p : ι → Bool) {a : ι → ℝ} (ha : ∀ i, 0 < a i) (w : EuclideanSpace ℝ ι) :
    𝓕 (heckeParityGaussian p a) w =
      ∏ i, (if p i then -Complex.I * (w i : ℂ)/(a i : ℂ) else 1) *
        (1/(a i : ℂ)^(1/2 : ℂ) * Complex.exp (-Real.pi/(a i : ℂ)*(w i : ℂ)^2)) := by
  classical
  change 𝓕 (fun x : EuclideanSpace ℝ ι =>
    ∏ i, (fun y : ℝ => if p i then heckeOddGaussian (a i) y else heckeRealGaussian (a i) y) (x i)) w = _
  rw [fourier_euclidean_product (fun i y =>
    if p i then heckeOddGaussian (a i) y else heckeRealGaussian (a i) y)]
  apply Finset.prod_congr rfl
  intro i hi
  cases hp : p i
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    exact congrFun (fourier_heckeRealGaussian (ha i)) (w i)
  · simp only [↓reduceIte]
    exact fourier_heckeOddGaussian (ha i) (w i)

theorem fourier_heckeParityGaussian_zero {ι : Type*} [Fintype ι]
    (p : ι → Bool) {a : ι → ℝ} (ha : ∀ i, 0 < a i) (hp : ∃ i, p i = true) :
    𝓕 (heckeParityGaussian p a) 0 = 0 := by
  classical
  rw [fourier_heckeParityGaussian p ha]
  obtain ⟨i, hi⟩ := hp
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi]



noncomputable def heckeNormalizedGaussian (odd : Bool) (a x : ℝ) : ℂ :=
  (if odd then (Real.sqrt a * x : ℝ) else 1) * heckeRealGaussian a x

theorem cpow_half_ofReal_eq_sqrt {a : ℝ} (ha : 0 ≤ a) :
    (a : ℂ)^(1/2 : ℂ) = (Real.sqrt a : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha]
  norm_num

theorem fourier_heckeNormalizedGaussian (odd : Bool) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    𝓕 (heckeNormalizedGaussian odd a) t =
      (if odd then -Complex.I else 1) / (Real.sqrt a : ℂ) *
        heckeNormalizedGaussian odd a⁻¹ t := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hs0 : (Real.sqrt a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne'
  have hs : (Real.sqrt a : ℂ)^2 = (a : ℂ) := by
    norm_cast
    exact Real.sq_sqrt ha.le
  cases odd
  · have hf : heckeNormalizedGaussian false a = heckeRealGaussian a := by
      ext x; simp [heckeNormalizedGaussian]
    rw [hf, fourier_heckeRealGaussian ha]
    simp only [Bool.false_eq_true, ↓reduceIte, heckeNormalizedGaussian,
      Complex.ofReal_one, one_mul, heckeRealGaussian, cpow_half_ofReal_eq_sqrt ha.le,
      Complex.ofReal_inv]
    congr 2
  · have hf : heckeNormalizedGaussian true a =
        (Real.sqrt a : ℂ) • heckeOddGaussian a := by
      ext x
      simp [heckeNormalizedGaussian, heckeOddGaussian, Complex.ofReal_mul, mul_assoc]
    have hlin := congrFun (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume
      (innerₗ ℝ) (heckeOddGaussian a) (Real.sqrt a : ℂ)) t
    change 𝓕 ((Real.sqrt a : ℂ) • heckeOddGaussian a) t =
      (Real.sqrt a : ℂ) * 𝓕 (heckeOddGaussian a) t at hlin
    rw [hf, hlin, fourier_heckeOddGaussian ha]
    simp only [↓reduceIte, heckeNormalizedGaussian, heckeRealGaussian,
      cpow_half_ofReal_eq_sqrt ha.le, Real.sqrt_inv, Complex.ofReal_mul,
      Complex.ofReal_inv]
    have hexp : Complex.exp (-Real.pi/(a : ℂ)*(t : ℂ)^2) =
        Complex.exp (-Real.pi*(a : ℂ)⁻¹*(t : ℂ)^2) := by congr 1
    rw [hexp]
    field_simp [ha0, hs0]
    rw [← hs]
    ring

theorem norm_heckeNormalizedGaussian_le (odd : Bool) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖heckeNormalizedGaussian odd a x‖ ≤ Real.exp (-(Real.pi*a/2)*x^2) := by
  have hs : (Real.sqrt a * |x|)^2 = a*x^2 := by
    rw [mul_pow, Real.sq_sqrt ha.le, sq_abs]
  have hxexp : Real.sqrt a * |x| ≤ Real.exp ((Real.pi*a/2)*x^2) := by
    have hpoly : Real.sqrt a * |x| ≤ 1 + (Real.sqrt a * |x|)^2 := by
      nlinarith [sq_nonneg (Real.sqrt a * |x| - 1)]
    calc
      _ ≤ 1 + a*x^2 := by simpa only [hs] using hpoly
      _ ≤ Real.exp (a*x^2) := by linarith [Real.add_one_le_exp (a*x^2)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Real.two_le_pi, sq_nonneg x])
  simp only [heckeNormalizedGaussian, norm_mul, heckeRealGaussian_ofReal,
    Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  cases odd
  · simp only [Bool.false_eq_true, ↓reduceIte, abs_one, one_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, sq_nonneg x]
  · simp only [↓reduceIte, abs_mul, abs_of_nonneg (Real.sqrt_nonneg a)]
    calc
      _ ≤ Real.exp ((Real.pi*a/2)*x^2) * Real.exp (-Real.pi*a*x^2) :=
        mul_le_mul_of_nonneg_right hxexp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring



/-- Unit-compatible parity kernel: each odd coordinate carries `sqrt(a_i)*x_i`. -/
noncomputable def heckeParityKernel {ι : Type*} [Fintype ι]
    (p : ι → Bool) (a : ι → ℝ) (x : EuclideanSpace ℝ ι) : ℂ :=
  ∏ i, heckeNormalizedGaussian (p i) (a i) (x i)

theorem continuous_heckeParityKernel {ι : Type*} [Fintype ι]
    (p : ι → Bool) (a : ι → ℝ) : Continuous (heckeParityKernel p a) := by
  unfold heckeParityKernel heckeNormalizedGaussian heckeRealGaussian
  apply continuous_finsetProd
  intro i hi
  cases p i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

theorem fourier_heckeParityKernel {ι : Type*} [Fintype ι]
    (p : ι → Bool) {a : ι → ℝ} (ha : ∀ i, 0 < a i) (w : EuclideanSpace ℝ ι) :
    𝓕 (heckeParityKernel p a) w =
      (∏ i, (if p i then -Complex.I else 1) / (Real.sqrt (a i) : ℂ)) *
        heckeParityKernel p (fun i => (a i)⁻¹) w := by
  unfold heckeParityKernel
  rw [fourier_euclidean_product (fun i => heckeNormalizedGaussian (p i) (a i)),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact fourier_heckeNormalizedGaussian (p i) (ha i) (w i)

theorem norm_heckeParityKernel_le {ι : Type*} [Fintype ι]
    (p : ι → Bool) {a : ι → ℝ} (ha : ∀ i, 0 < a i) (x : EuclideanSpace ℝ ι) :
    ‖heckeParityKernel p a x‖ ≤ Real.exp (-Real.pi * ∑ i, (a i/2)*(x i)^2) := by
  unfold heckeParityKernel
  rw [norm_prod]
  calc
    _ ≤ ∏ i, Real.exp (-(Real.pi*a i/2)*(x i)^2) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      exact fun i _ => norm_heckeNormalizedGaussian_le (p i) (ha i) (x i)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem heckeParityKernel_zero {ι : Type*} [Fintype ι]
    (p : ι → Bool) (a : ι → ℝ) (hp : ∃ i, p i = true) :
    heckeParityKernel p a 0 = 0 := by
  classical
  obtain ⟨i, hi⟩ := hp
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [heckeNormalizedGaussian, hi]

theorem fourier_heckeParityKernel_zero {ι : Type*} [Fintype ι]
    (p : ι → Bool) {a : ι → ℝ} (ha : ∀ i, 0 < a i) (hp : ∃ i, p i = true) :
    𝓕 (heckeParityKernel p a) 0 = 0 := by
  rw [fourier_heckeParityKernel p ha, heckeParityKernel_zero p _ hp, mul_zero]

end UnitDistance.NumberFieldAnalysis
