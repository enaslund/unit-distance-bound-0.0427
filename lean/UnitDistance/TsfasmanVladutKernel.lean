module

public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.ExpDecay

@[expose] public section
set_option backward.privateInPublic true


/-!
# The Tsfasman–Vlăduţ test kernel and its actual bilateral transform

The half-line exponential reductions follow the elementary approach in
Chris Birkbeck's AINTLIB DedekindResidue/Lemma2.lean and Lemma5.lean,
commit a302aeacd86053f9d5f991fbbf664e1cc1051d08 (2026, Apache-2.0).
See third-party/aintlib for the retained license and provenance. Only Mathlib
is imported here; no Dedekind-residue or explicit-formula theorem is assumed.
-/

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology

namespace UnitDistance.NumberFieldAnalysis

def tvKernel (e x : ℝ) : ℂ := (Real.exp (-e*|x|) / Real.cosh (x/2) : ℝ)

def tvTransform (e : ℝ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, tvKernel e x * Complex.exp ((s-1/2)*x)

@[simp] theorem tvKernel_neg (e x : ℝ) : tvKernel e (-x) = tvKernel e x := by
  simp only [tvKernel, abs_neg, neg_div, Real.cosh_neg]

@[simp] theorem tvKernel_zero (e : ℝ) : tvKernel e 0 = 1 := by simp [tvKernel]

@[simp] theorem tvKernel_im (e x : ℝ) : (tvKernel e x).im = 0 := rfl

theorem tvKernel_re_pos (e x : ℝ) : 0 < (tvKernel e x).re :=
  div_pos (Real.exp_pos _) (Real.cosh_pos _)

theorem continuous_tvKernel (e : ℝ) : Continuous (tvKernel e) := by
  unfold tvKernel
  exact Complex.continuous_ofReal.comp
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).div
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
      (fun x => (Real.cosh_pos (x/2)).ne'))

theorem norm_tvKernel (e x : ℝ) :
    ‖tvKernel e x‖ = Real.exp (-e*|x|)/Real.cosh (x/2) := by
  rw [tvKernel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (Real.cosh_pos _))]

theorem exp_abs_half_le_two_cosh (x : ℝ) : Real.exp (|x|/2) ≤ 2*Real.cosh (x/2) := by
  have hc : Real.cosh (|x|/2) = Real.cosh (x/2) := by
    simpa only [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)] using Real.cosh_abs (x := x/2)
  rw [← hc, Real.cosh_eq]
  linarith [Real.exp_pos (-(|x|/2))]

/-- The additional half-unit of exponential decay comes from the actual cosh denominator. -/
theorem norm_tvKernel_le (e x : ℝ) : ‖tvKernel e x‖ ≤ 2*Real.exp (-(e+1/2)*|x|) := by
  rw [norm_tvKernel]
  apply (div_le_iff₀ (Real.cosh_pos _)).mpr
  calc
    Real.exp (-e*|x|) = Real.exp (-(e+1/2)*|x|)*Real.exp (|x|/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(e+1/2)*|x|)*(2*Real.cosh (x/2)) :=
      mul_le_mul_of_nonneg_left (exp_abs_half_le_two_cosh x) (Real.exp_pos _).le
    _ = _ := by ring

theorem tv_integrable_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a*|x|)) := by
  have hn : IntegrableOn (fun x : ℝ => Real.exp (-a*|x|)) (Iic 0) :=
    (integrableOn_exp_mul_Iic ha 0).congr_fun
      (fun x hx => by simp [abs_of_nonpos (show x ≤ 0 from hx)]) measurableSet_Iic
  have hp : IntegrableOn (fun x : ℝ => Real.exp (-a*|x|)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 ha).congr_fun
      (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hp

theorem tv_integral_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, Real.exp (-a*|x|)) = 2/a := by
  have hn : (∫ x : ℝ in Iic 0, Real.exp (-a*|x|)) = 1/a := by
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun x hx => show Real.exp (-a*|x|) = Real.exp (a*x) by rw [abs_of_nonpos hx]; congr 1; ring)]
    simpa using integral_exp_mul_Iic ha 0
  have hp : (∫ x : ℝ in Ioi 0, Real.exp (-a*|x|)) = 1/a := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => show Real.exp (-a*|x|) = Real.exp (-a*x) by rw [abs_of_pos hx])]
    simpa using integral_exp_mul_Ioi (by linarith : -a<0) 0
  rw [← integral_add_compl measurableSet_Iic (tv_integrable_exp_neg_abs ha), compl_Iic, hn, hp]
  ring

theorem integrable_tvKernel {e : ℝ} (he : 0 < e) : Integrable (tvKernel e) :=
  ((tv_integrable_exp_neg_abs (by linarith : 0 < e+1/2)).const_mul 2).mono'
    (continuous_tvKernel e).aestronglyMeasurable (Eventually.of_forall (norm_tvKernel_le e))

theorem continuous_tvIntegrand (e : ℝ) (s : ℂ) :
    Continuous (fun x : ℝ => tvKernel e x*Complex.exp ((s-1/2)*x)) := by
  exact (continuous_tvKernel e).mul
    ((continuous_const.mul Complex.continuous_ofReal).cexp)

theorem norm_tvIntegrand_le (e : ℝ) (s : ℂ) (x : ℝ) :
    ‖tvKernel e x*Complex.exp ((s-1/2)*x)‖ ≤
      2*Real.exp (-(e+1/2-|s.re-1/2|)*|x|) := by
  rw [norm_mul, Complex.norm_exp]
  have hr : ((s-1/2)*(x:ℂ)).re = (s.re-1/2)*x := by simp
  rw [hr]
  calc
    _ ≤ (2*Real.exp (-(e+1/2)*|x|))*Real.exp ((s.re-1/2)*x) :=
      mul_le_mul_of_nonneg_right (norm_tvKernel_le e x) (Real.exp_pos _).le
    _ = 2*Real.exp (-(e+1/2)*|x|+(s.re-1/2)*x) := by rw [Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      have h := le_abs_self ((s.re-1/2)*x)
      rw [abs_mul] at h
      nlinarith

theorem integrable_tvIntegrand {e : ℝ} {s : ℂ} (hs : |s.re-1/2| < 1/2+e) :
    Integrable (fun x : ℝ => tvKernel e x*Complex.exp ((s-1/2)*x)) :=
  ((tv_integrable_exp_neg_abs (by linarith : 0 < e+1/2-|s.re-1/2|)).const_mul 2).mono'
    (continuous_tvIntegrand e s).aestronglyMeasurable (Eventually.of_forall (norm_tvIntegrand_le e s))

theorem norm_tvTransform_le {e : ℝ} {s : ℂ} (hs : |s.re-1/2| < 1/2+e) :
    ‖tvTransform e s‖ ≤ 4/(e+1/2-|s.re-1/2|) := by
  calc
    _ ≤ ∫ x : ℝ, ‖tvKernel e x*Complex.exp ((s-1/2)*x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, 2*Real.exp (-(e+1/2-|s.re-1/2|)*|x|) :=
      integral_mono (integrable_tvIntegrand hs).norm
        ((tv_integrable_exp_neg_abs (by linarith : 0 < e+1/2-|s.re-1/2|)).const_mul 2)
        (norm_tvIntegrand_le e s)
    _ = _ := by
      rw [integral_const_mul, tv_integral_exp_neg_abs (by linarith : 0 < e+1/2-|s.re-1/2|)]
      ring

theorem norm_tvTransform_le_closed_strip {e : ℝ} (he : 0 < e) {s : ℂ}
    (h₀ : 0 ≤ s.re) (h₁ : s.re ≤ 1) : ‖tvTransform e s‖ ≤ 4/e := by
  have ha : |s.re-1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  exact (norm_tvTransform_le (by linarith)).trans
    (div_le_div_of_nonneg_left (by norm_num) he (by linarith))

theorem integrable_tvKernel_mul_exp {e c : ℝ} (hc : |c| < 1/2+e) :
    Integrable (fun x : ℝ => tvKernel e x*(Real.exp (c*x) : ℂ)) := by
  have h := integrable_tvIntegrand (e := e) (s := (c:ℂ)+1/2) (by simpa using hc)
  convert h using 1
  funext x
  rw [add_sub_cancel_right, Complex.ofReal_exp, Complex.ofReal_mul]

theorem tv_abs_mul_exp_bound {b : ℝ} (hb : 0 < b) (x : ℝ) :
    |x| *Real.exp (-b*|x|) ≤ (2/b)*Real.exp (-(b/2)*|x|) := by
  have ht : b*|x| ≤ 2*Real.exp ((b/2)*|x|) := by
    have h := Real.add_one_le_exp ((b/2)*|x|)
    linarith
  have hx : |x| ≤ (2/b)*Real.exp ((b/2)*|x|) := by
    have h := (le_div_iff₀ hb).mpr (show |x| * b ≤ 2*Real.exp ((b/2)*|x|) by nlinarith [ht])
    simpa only [div_mul_eq_mul_div] using h
  calc
    _ ≤ ((2/b)*Real.exp ((b/2)*|x|))*Real.exp (-b*|x|) :=
      mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem tvIntegrand_hasDerivAt (e x : ℝ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => tvKernel e x*Complex.exp ((z-1/2)*x))
      ((tvKernel e x*Complex.exp ((s-1/2)*x))*(x:ℂ)) s := by
  simpa only [id_eq, one_mul, ← mul_assoc] using!
    ((((hasDerivAt_id s).sub_const (1/2)).mul_const (x:ℂ)).cexp.const_mul (tvKernel e x))

/-- Differentiation is justified by an actual locally uniform integrable
exponential bound, throughout the complete convergence strip. -/
theorem hasDerivAt_tvTransform {e : ℝ} {s : ℂ} (hs : |s.re-1/2| < 1/2+e) :
    HasDerivAt (tvTransform e)
      (∫ x : ℝ, (tvKernel e x*Complex.exp ((s-1/2)*x))*(x:ℂ)) s := by
  let b : ℝ := (e+1/2-|s.re-1/2|)/2
  have hb : 0 < b := by dsimp [b]; linarith
  let F' : ℂ → ℝ → ℂ := fun z x => (tvKernel e x*Complex.exp ((z-1/2)*x))*(x:ℂ)
  have hbound : ∀ᵐ x : ℝ, ∀ z ∈ Metric.ball s b,
      ‖F' z x‖ ≤ (4/b)*Real.exp (-(b/2)*|x|) := by
    refine Eventually.of_forall (fun x z hz => ?_)
    have hr₀ : |z.re-s.re| ≤ dist z s := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (z-s)
    have hr₁ : |z.re-1/2| ≤ |z.re-s.re|+|s.re-1/2| := by
      have h := norm_add_le (z.re-s.re) (s.re-1/2)
      simpa only [Real.norm_eq_abs, sub_add_sub_cancel] using h
    have hr : b ≤ e+1/2-|z.re-1/2| := by
      have hz' : dist z s < b := hz
      dsimp [b] at *
      linarith
    have hi : ‖tvKernel e x*Complex.exp ((z-1/2)*x)‖ ≤ 2*Real.exp (-b*|x|) := by
      refine (norm_tvIntegrand_le e z x).trans ?_
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      nlinarith [abs_nonneg x]
    calc
      ‖F' z x‖ = ‖tvKernel e x*Complex.exp ((z-1/2)*x)‖*|x| := by
        simp only [F', norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (2*Real.exp (-b*|x|))*|x| := mul_le_mul_of_nonneg_right hi (abs_nonneg x)
      _ = 2*(|x| *Real.exp (-b*|x|)) := by ring
      _ ≤ 2*((2/b)*Real.exp (-(b/2)*|x|)) := mul_le_mul_of_nonneg_left (tv_abs_mul_exp_bound hb x) (by norm_num)
      _ = _ := by ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z x => tvKernel e x*Complex.exp ((z-1/2)*x))
    (F' := F') (bound := fun x : ℝ => (4/b)*Real.exp (-(b/2)*|x|))
    (Metric.ball_mem_nhds s hb)
    (Eventually.of_forall (fun z => (continuous_tvIntegrand e z).aestronglyMeasurable))
    (integrable_tvIntegrand hs)
    ((continuous_tvIntegrand e s).mul Complex.continuous_ofReal).aestronglyMeasurable
    hbound ((tv_integrable_exp_neg_abs (half_pos hb)).const_mul (4/b))
    (Eventually.of_forall (fun x z _ => tvIntegrand_hasDerivAt e x z))
  exact h.2

theorem differentiableAt_tvTransform {e : ℝ} {s : ℂ} (hs : |s.re-1/2| < 1/2+e) :
    DifferentiableAt ℂ (tvTransform e) s := (hasDerivAt_tvTransform hs).differentiableAt

theorem differentiableOn_tvTransform (e : ℝ) :
    DifferentiableOn ℂ (tvTransform e) {s : ℂ | -e < s.re ∧ s.re < 1+e} := by
  intro s hs
  exact (differentiableAt_tvTransform (abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)).differentiableWithinAt

theorem tvTransform_diffContOnCl {e : ℝ} (he : 0 < e) :
    DiffContOnCl ℂ (tvTransform e) (Complex.re ⁻¹' Ioo (0:ℝ) 1) := by
  apply DifferentiableOn.diffContOnCl
  apply (differentiableOn_tvTransform e).mono
  intro z hz
  have hc : closure (Complex.re ⁻¹' Ioo (0:ℝ) 1) ⊆ Complex.re ⁻¹' Icc (0:ℝ) 1 :=
    closure_minimal (fun _ h => Ioo_subset_Icc_self h) (isClosed_Icc.preimage Complex.continuous_re)
  obtain ⟨h₀, h₁⟩ := hc hz
  exact ⟨by linarith, by linarith⟩

end UnitDistance.NumberFieldAnalysis
