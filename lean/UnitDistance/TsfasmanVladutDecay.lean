module

public import UnitDistance.TsfasmanVladutHalfIntegrability
public import UnitDistance.TsfasmanVladutHalfFourier
public import UnitDistance.TsfasmanVladutKernel

@[expose] public section
set_option backward.privateInPublic true


/-! Actual quadratic vertical decay of the Tsfasman–Vlăduţ transform.
Two half-line integrations by parts cancel the shared endpoint value. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Complex
open scoped Topology
namespace UnitDistance.NumberFieldAnalysis

theorem tvHalfProfile_fourier_twice {b : ℝ} (hb : 0 < b+1/2) (t : ℝ) :
    ((t:ℂ)*Complex.I)^2*tvHalfFourier (fun x => (tvHalfProfile b x : ℂ)) t =
      -((t:ℂ)*Complex.I)-(b:ℂ)+tvHalfFourier (fun x => (tvHalfSecond b x : ℂ)) t := by
  have h := tvHalfFourier_twice
    (fun x _ => (hasDerivAt_tvHalfProfile b x).ofReal_comp)
    (fun x _ => (hasDerivAt_tvHalfDeriv b x).ofReal_comp)
    (integrableOn_tvHalfProfile hb).ofReal (integrableOn_tvHalfDeriv hb).ofReal
    (integrableOn_tvHalfSecond hb).ofReal
    (Complex.continuous_ofReal.tendsto 0 |>.comp (tendsto_tvHalfProfile_atTop hb))
    (Complex.continuous_ofReal.tendsto 0 |>.comp (tendsto_tvHalfDeriv_atTop hb)) t
  simpa only [tvHalfProfile_zero, tvHalfDeriv_zero, Complex.ofReal_one,
    Complex.ofReal_neg, mul_one, sub_eq_add_neg] using h

theorem norm_tvHalfSecond_fourier_le {b : ℝ} (hb : 0 < b+1/2) (t : ℝ) :
    ‖tvHalfFourier (fun x => (tvHalfSecond b x : ℂ)) t‖ ≤
      2*((|b|+1/2)^2+1/4)/(b+1/2) := by
  refine (norm_tvHalfFourier_le _ t).trans ?_
  simpa only [Complex.norm_real, Real.norm_eq_abs] using integral_abs_tvHalfSecond_le hb

theorem tvIntegrand_eq_halfProfile (e : ℝ) (s : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    tvKernel e x*Complex.exp ((s-1/2)*x) =
      (tvHalfProfile (e-(s.re-1/2)) x : ℂ)*tvOscillation s.im x := by
  have hs : (s-1/2)*(x:ℂ) = (((s.re-1/2)*x:ℝ):ℂ)+(s.im:ℂ)*I*x := by
    apply Complex.ext <;> simp <;> ring
  have he : Real.exp (-(e-(s.re-1/2))*x) = Real.exp (-e*x)*Real.exp ((s.re-1/2)*x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [tvKernel, tvHalfProfile, abs_of_nonneg hx, he, hs, Complex.exp_add]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp]
  dsimp [tvOscillation]
  ring

theorem tvTransform_eq_halfFourier {e : ℝ} {s : ℂ}
    (hs : |s.re-1/2| < 1/2+e) :
    tvTransform e s =
      tvHalfFourier (fun x => (tvHalfProfile (e-(s.re-1/2)) x : ℂ)) s.im+
      tvHalfFourier (fun x => (tvHalfProfile (e+(s.re-1/2)) x : ℂ)) (-s.im) := by
  let f : ℝ → ℂ := fun x => tvKernel e x*Complex.exp ((s-1/2)*x)
  have hp : (∫ x : ℝ in Ioi 0, f x) =
      tvHalfFourier (fun x => (tvHalfProfile (e-(s.re-1/2)) x : ℂ)) s.im := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact tvIntegrand_eq_halfProfile e s hx.le
  have hn : (∫ x : ℝ in Iic 0, f x) =
      tvHalfFourier (fun x => (tvHalfProfile (e+(s.re-1/2)) x : ℂ)) (-s.im) := by
    rw [← show (∫ x : ℝ in Ioi 0, f (-x)) = ∫ x : ℝ in Iic 0, f x by
      simpa using integral_comp_neg_Ioi 0 f]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have h : f (-x) = tvKernel e x*Complex.exp (((1-s)-1/2)*x) := by
      dsimp [f]
      rw [tvKernel_neg, Complex.ofReal_neg]
      congr 2
      ring
    change f (-x) = _
    rw [h, tvIntegrand_eq_halfProfile e (1-s) hx.le]
    congr 2 <;> simp <;> ring
  change (∫ x : ℝ, f x) = _
  rw [← integral_add_compl measurableSet_Iic (integrable_tvIntegrand hs), compl_Iic, hn, hp,
    add_comm]

theorem tvTransform_second_identity {e : ℝ} {s : ℂ}
    (hs : |s.re-1/2| < 1/2+e) :
    ((s.im:ℂ)*I)^2*tvTransform e s = -(2*e:ℂ)+
      tvHalfFourier (fun x => (tvHalfSecond (e-(s.re-1/2)) x : ℂ)) s.im+
      tvHalfFourier (fun x => (tvHalfSecond (e+(s.re-1/2)) x : ℂ)) (-s.im) := by
  obtain ⟨hl, hu⟩ := abs_lt.mp hs
  have h₁ := tvHalfProfile_fourier_twice (b := e-(s.re-1/2)) (by linarith) s.im
  have h₂ := tvHalfProfile_fourier_twice (b := e+(s.re-1/2)) (by linarith) (-s.im)
  have hsq : (((-s.im:ℝ):ℂ)*I)^2 = ((s.im:ℂ)*I)^2 := by push_cast; ring
  rw [hsq] at h₂
  rw [tvTransform_eq_halfFourier hs, mul_add, h₁, h₂]
  push_cast
  ring

theorem tvTransform_quadratic_bound {e : ℝ} {s : ℂ}
    (hs : |s.re-1/2| < 1/2+e) :
    s.im^2*‖tvTransform e s‖ ≤ 2*|e|+
      2*((|e-(s.re-1/2)|+1/2)^2+1/4)/(e-(s.re-1/2)+1/2)+
      2*((|e+(s.re-1/2)|+1/2)^2+1/4)/(e+(s.re-1/2)+1/2) := by
  obtain ⟨hl, hu⟩ := abs_lt.mp hs
  have h₁ := norm_tvHalfSecond_fourier_le (b := e-(s.re-1/2)) (by linarith) s.im
  have h₂ := norm_tvHalfSecond_fourier_le (b := e+(s.re-1/2)) (by linarith) (-s.im)
  have h := congrArg norm (tvTransform_second_identity hs)
  simp only [norm_mul, norm_pow, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] at h
  rw [h]
  calc
    _ ≤ ‖-(2*e:ℂ)‖+
        ‖tvHalfFourier (fun x => (tvHalfSecond (e-(s.re-1/2)) x : ℂ)) s.im‖+
        ‖tvHalfFourier (fun x => (tvHalfSecond (e+(s.re-1/2)) x : ℂ)) (-s.im)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [norm_neg, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
      linarith

theorem tv_second_bound_uniform {e a b : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hae : a < e)
    (hb : |b| ≤ e+a+1/2) (hd : e-a ≤ b+1/2) :
    2*((|b|+1/2)^2+1/4)/(b+1/2) ≤ 2*((e+a+1)^2+1/4)/(e-a) := by
  have hden : 0 < e-a := sub_pos.mpr hae
  have hn : (|b|+1/2)^2 ≤ (e+a+1)^2 := by
    have h₀ := abs_nonneg b
    nlinarith
  apply (div_le_div_of_nonneg_left (by positivity) hden hd).trans
  apply div_le_div_of_nonneg_right _ hden.le
  linarith

def tvDecayConstant (e a : ℝ) : ℝ := 2*e+4*((e+a+1)^2+1/4)/(e-a)

theorem tvDecayConstant_nonneg {e a : ℝ} (he : 0 < e) (hae : a < e) :
    0 ≤ tvDecayConstant e a := by
  dsimp [tvDecayConstant]
  positivity

theorem tvTransform_quadratic_bound_strip {e a : ℝ}
    (he : 0 < e) (ha : 0 ≤ a) (hae : a < e) {s : ℂ}
    (h₀ : -a ≤ s.re) (h₁ : s.re ≤ 1+a) :
    s.im^2*‖tvTransform e s‖ ≤ tvDecayConstant e a := by
  have hc : |s.re-1/2| ≤ a+1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hm : |e-(s.re-1/2)| ≤ e+a+1/2 := by
    calc
      _ ≤ |e|+|s.re-1/2| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_pos he]; linarith
  have hp : |e+(s.re-1/2)| ≤ e+a+1/2 := by
    calc
      _ ≤ |e|+|s.re-1/2| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_pos he]; linarith
  have h := tvTransform_quadratic_bound (e := e) (s := s) (by linarith)
  have hm' := tv_second_bound_uniform he ha hae hm (by linarith : e-a ≤ e-(s.re-1/2)+1/2)
  have hp' := tv_second_bound_uniform he ha hae hp (by linarith : e-a ≤ e+(s.re-1/2)+1/2)
  rw [abs_of_pos he] at h
  calc
    _ ≤ 2*e+2*((e+a+1)^2+1/4)/(e-a)+2*((e+a+1)^2+1/4)/(e-a) := by linarith
    _ = _ := by dsimp [tvDecayConstant]; ring

theorem norm_tvTransform_le_div_max_sq {e a : ℝ}
    (he : 0 < e) (ha : 0 ≤ a) (hae : a < e) {s : ℂ}
    (h₀ : -a ≤ s.re) (h₁ : s.re ≤ 1+a) :
    ‖tvTransform e s‖ ≤ (tvDecayConstant e a+4/(e-a))/(max |s.im| 1)^2 := by
  have hden : 0 < e-a := sub_pos.mpr hae
  have hC := tvDecayConstant_nonneg he hae
  rcases le_total |s.im| 1 with ht | ht
  · rw [max_eq_right ht, one_pow, div_one]
    have hc : |s.re-1/2| ≤ a+1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h := norm_tvTransform_le (e := e) (s := s) (by linarith)
    have h' : 4/(e+1/2-|s.re-1/2|) ≤ 4/(e-a) :=
      div_le_div_of_nonneg_left (by norm_num) hden (by linarith)
    linarith
  · rw [max_eq_left ht, sq_abs]
    have hpos : 0 < s.im^2 := by nlinarith [sq_abs s.im]
    apply (le_div_iff₀ hpos).mpr
    have h := tvTransform_quadratic_bound_strip he ha hae h₀ h₁
    have hnonneg : 0 ≤ 4/(e-a) := by positivity
    nlinarith

theorem tvTransform_decay_enlarged_strip {e a : ℝ}
    (he : 0 < e) (ha : 0 ≤ a) (hae : a < e) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ t : ℝ, -a ≤ σ → σ ≤ 1+a →
      ‖tvTransform e ((σ:ℂ)+(t:ℂ)*I)‖ ≤ M/(max |t| 1)^2 := by
  refine ⟨tvDecayConstant e a+4/(e-a), ?_, ?_⟩
  · exact add_nonneg (tvDecayConstant_nonneg he hae) (by positivity)
  · intro σ t h₀ h₁
    simpa using norm_tvTransform_le_div_max_sq he ha hae
      (s := (σ:ℂ)+(t:ℂ)*I) (by simpa using h₀) (by simpa using h₁)

theorem tvKernel_fourier_eq_transform (e t : ℝ) :
    (∫ x : ℝ, tvKernel e x*Complex.exp (((t*x:ℝ):ℂ)*I)) =
      tvTransform e ((1/2:ℂ)+(t:ℂ)*I) := by
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  push_cast
  ring

theorem tvKernel_quadratic_fourier_decay {e : ℝ} (he : 0 < e) :
    ∃ C γ₀ : ℝ, 1 ≤ γ₀ ∧ ∀ t : ℝ, γ₀ ≤ |t| →
      ‖∫ x : ℝ, tvKernel e x*Complex.exp (((t*x:ℝ):ℂ)*I)‖ ≤ C/t^2 := by
  refine ⟨tvDecayConstant e 0, 1, le_rfl, ?_⟩
  intro t ht
  rw [tvKernel_fourier_eq_transform]
  have hpos : 0 < t^2 := by nlinarith [sq_abs t]
  apply (le_div_iff₀ hpos).mpr
  have h := tvTransform_quadratic_bound_strip he (a := 0) le_rfl he
    (s := (1/2:ℂ)+(t:ℂ)*I) (by simp) (by norm_num)
  simpa [mul_comm] using h

end UnitDistance.NumberFieldAnalysis
