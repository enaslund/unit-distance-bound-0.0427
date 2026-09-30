module

public import UnitDistance.TsfasmanVladutPrimeSide
public import UnitDistance.TsfasmanVladutScaledDecay
public import UnitDistance.TsfasmanVladutKernelPositivity
public import UnitDistance.TsfasmanVladutArchimedean

@[expose] public section
set_option backward.privateInPublic true


/-!
# Specializing the actual Weil formula to the unconditional sech kernel

The test-function admissibility and positivity here are proved from the
explicit kernel. The upstream formula is the attributed source port in
`third-party/aintlib`; no GRH or relative-Hecke hypothesis is imposed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Topology NumberField
open scoped NNReal ENNReal
namespace UnitDistance.NumberFieldAnalysis

@[simp] theorem paperPhi_tvKernel (e : ℝ) :
    DedekindResidue.paperPhi (tvKernel e) = tvTransform e := rfl

theorem tendsto_tv_boundary {e σ : ℝ} (he : 0 < e)
    (hσ : 0 < σ) (hσl : -1 ≤ σ) (hσr : σ ≤ 2)
    (l : Filter ℝ) (habs : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ => DedekindResidue.rhoFT
      (fun x => ((DedekindResidue.poitouKernel σ x : ℝ) : ℂ)) t *
      DedekindResidue.gammaFT (tvKernel e) t) l (𝓝 0) := by
  obtain ⟨C, γ₀, hγ₀, hφ⟩ := tvKernel_quadratic_fourier_decay he
  exact DedekindResidue.tendsto_rhoFT_mul_gammaFT_of_decay hσ hσl hσr
    (DedekindResidue.norm_gammaFT_le_of_fourier_decay (integrable_tvKernel he)
      (integrableOn_tvKernel_diffQuot_window he.le) hγ₀ hφ) l habs

theorem tendsto_tv_boundary_half {e σ : ℝ} (he : 0 < e)
    (hσ : 0 < σ) (hσl : -1 ≤ σ) (hσr : σ ≤ 2)
    (l : Filter ℝ) (habs : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ => DedekindResidue.rhoFT
      (fun x => ((DedekindResidue.poitouKernel σ x : ℝ) : ℂ)) t *
      DedekindResidue.gammaFT (fun x : ℝ => tvKernel e (x/2)/2) t) l (𝓝 0) := by
  obtain ⟨C, γ₀, hγ₀, hφ⟩ := tvKernel_half_quadratic_fourier_decay he
  have hFdiv : IntegrableOn (fun x : ℝ =>
      ((fun x : ℝ => tvKernel e (x/2)/2) 0 - (fun x : ℝ => tvKernel e (x/2)/2) x)/(x:ℂ))
      (Ioc (-1) 1) := by
    simpa only [zero_div] using DedekindResidue.integrableOn_halfScale_div
      (integrableOn_tvKernel_diffQuot_window he.le)
  exact DedekindResidue.tendsto_rhoFT_mul_gammaFT_of_decay hσ hσl hσr
    (DedekindResidue.norm_gammaFT_le_of_fourier_decay
      (DedekindResidue.integrable_halfScale (integrable_tvKernel he)) hFdiv hγ₀ hφ) l habs

theorem re_finsum_nonneg {ι : Type*} {f : ι → ℂ} (hf : ∀ i, 0 ≤ (f i).re) :
    0 ≤ (∑ᶠ i, f i).re := by
  classical
  by_cases hfin : (Function.support f).Finite
  · rw [finsum_eq_sum f hfin, Complex.re_sum]
    exact Finset.sum_nonneg (fun i _ => hf i)
  · rw [finsum_of_infinite_support hfin]
    simp

variable (K : Type*) [Field K] [NumberField K]

/-- Every actual zero contribution is nonnegative, since the zeros of the
ordinary entire completion lie in the closed strip and the actual transform
has nonnegative real part throughout that strip. -/
theorem tv_zero_sum_re_nonneg {e : ℝ} (he : 0 < e) (U : Set ℂ) :
    0 ≤ (∑ᶠ ρ, ((MeromorphicOn.divisor (DedekindResidue.completedDedekindZetaEntire K) U ρ : ℤ) : ℂ) *
      tvTransform e ρ).re := by
  apply re_finsum_nonneg
  intro ρ
  by_cases hρ : MeromorphicOn.divisor (DedekindResidue.completedDedekindZetaEntire K) U ρ = 0
  · simp [hρ]
  have hzero := DedekindResidue.completedDedekindZetaEntire_eq_zero_of_divisor_ne_zero K hρ
  obtain ⟨h₀, h₁⟩ := DedekindResidue.re_mem_of_completedDedekindZetaEntire_eq_zero K hzero
  have hdiv : 0 ≤ MeromorphicOn.divisor (DedekindResidue.completedDedekindZetaEntire K) U ρ :=
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (fun ζ _ => DedekindResidue.analyticAt_completedDedekindZetaEntire K ζ)) ρ
  simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
  exact mul_nonneg (by exact_mod_cast hdiv) (tvTransform_re_nonneg he h₀ h₁)


def tvWeilRhs (e a : ℝ) : ℂ :=
  (tvTransform e 0 + tvTransform e 1)
  + ((Real.log |NumberField.discr K| : ℝ) : ℂ)
  + ((-(((InfinitePlace.nrRealPlaces K : ℝ) + 2*(InfinitePlace.nrComplexPlaces K : ℝ)) *
      (Real.eulerMascheroniConstant + Real.log (8*Real.pi)) +
      (InfinitePlace.nrRealPlaces K : ℝ)*(Real.pi/2)) : ℝ) : ℂ)
  + ((InfinitePlace.nrRealPlaces K + 2*InfinitePlace.nrComplexPlaces K : ℕ) : ℂ) *
      (∫ y in Ioi (0:ℝ), ((1/(2*Real.sinh (y/2)) : ℝ) : ℂ)*(1-tvKernel e y))
  + ((InfinitePlace.nrRealPlaces K : ℕ) : ℂ) *
      (∫ y in Ioi (0:ℝ), ((1/(2*Real.cosh (y/2)) : ℝ) : ℂ)*(1-tvKernel e y))
  - (DedekindResidue.primeSideH K a (tvKernel e) 0 +
      DedekindResidue.primeSideH K a (tvKernel e) 0)

/-- Unconditional specialization of the Weil formula: its right-hand side
is the limit of actual zero sums, each having nonnegative real part. -/
theorem tvWeilRhs_re_nonneg {e a : ℝ} (he : 0 < e) (ha : 0 < a)
    (ha' : a ≤ 1/4) (hae : a < e) : 0 ≤ (tvWeilRhs K e a).re := by
  have hF := integrable_tvKernel he
  have hlip := lipschitzWith_tvKernel he.le
  have hdiv := integrableOn_tvKernel_diffQuot_window he.le
  have hdiv2 := memLp_two_tvKernel_diffQuot he.le
  have hc : |1/2+a| < 1/2+e := by
    rw [abs_of_pos (by linarith : 0 < 1/2+a)]
    linarith
  have hFa := integrable_tvKernel_mul_exp hc
  have hGlip := lipschitzWith_tvWeighted (e := e) (c := 1/2+a) (by linarith)
  have hEc := DedekindResidue.locallyBoundedVariationOn_poleWindow_add
    ha (by linarith : 0 < 1+a) hFa hGlip.continuous
  have hΦd : ∀ ζ : ℂ, -a ≤ ζ.re → ζ.re ≤ 1+a →
      DifferentiableAt ℂ (DedekindResidue.paperPhi (tvKernel e)) ζ := by
    intro ζ h₀ h₁
    exact differentiableAt_tvTransform (abs_lt.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨M, hM, hdecay⟩ := tvTransform_decay_enlarged_strip he ha.le hae
  have hB : ∀ σ t : ℝ, -a ≤ σ → σ ≤ 1+a →
      ‖DedekindResidue.paperPhi (tvKernel e) ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        M/max |t| 1 := by
    intro σ t h₀ h₁
    refine (hdecay σ t h₀ h₁).trans ?_
    have hm : 1 ≤ max |t| 1 := le_max_right _ _
    exact div_le_div_of_nonneg_left hM (by linarith) (by nlinarith)
  have hHc := continuous_primeSideH_tvKernel K ha hae.le
  obtain ⟨T, hT, hlim⟩ := DedekindResidue.weil_explicit_formula K ha ha' hF
    ((DedekindResidue.lipschitzWith_complex_re.comp hlip).locallyBoundedVariationOn univ)
    ((DedekindResidue.lipschitzWith_complex_im.comp hlip).locallyBoundedVariationOn univ)
    ((continuous_tvKernel e).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tvKernel_neg e) hdiv hdiv2
    (tendsto_tv_boundary he (by norm_num) (by norm_num) (by norm_num)
      atTop tendsto_abs_atTop_atTop)
    (tendsto_tv_boundary he (by norm_num) (by norm_num) (by norm_num)
      atBot tendsto_abs_atBot_atTop)
    (tendsto_tv_boundary_half he (by norm_num) (by norm_num) (by norm_num)
      atTop tendsto_abs_atTop_atTop)
    (tendsto_tv_boundary_half he (by norm_num) (by norm_num) (by norm_num)
      atBot tendsto_abs_atBot_atTop)
    hΦd hB (DedekindResidue.tendsto_div_max_mul_log_sq M) hFa
    ((DedekindResidue.lipschitzWith_complex_re.comp hGlip).locallyBoundedVariationOn univ)
    ((DedekindResidue.lipschitzWith_complex_im.comp hGlip).locallyBoundedVariationOn univ)
    (DedekindResidue.lipschitzWith_complex_re.comp_locallyBoundedVariationOn hEc)
    (DedekindResidue.lipschitzWith_complex_im.comp_locallyBoundedVariationOn hEc)
    (locallyBoundedVariationOn_primeSideH_tvKernel_re K ha hae.le)
    (locallyBoundedVariationOn_primeSideH_tvKernel_im K ha hae.le)
    (hHc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hHc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hlim' : Tendsto (fun n : ℕ => (∑ᶠ ρ,
      ((MeromorphicOn.divisor (DedekindResidue.completedDedekindZetaEntire K)
        (Ioo (-a) (1+a) ×ℂ Ioo (-(T n)) (T n)) ρ : ℤ) : ℂ)*tvTransform e ρ).re)
      atTop (𝓝 (tvWeilRhs K e a).re) := by
    simpa only [tvWeilRhs, paperPhi_tvKernel, tvKernel_zero, mul_one, Function.comp_def] using
      Complex.continuous_re.continuousAt.tendsto.comp hlim
  exact ge_of_tendsto hlim' (Eventually.of_forall (fun n => tv_zero_sum_re_nonneg K he _))


theorem tvKernel_arch_integral (e : ℝ) :
    (∫ y in Ioi (0:ℝ), ((1/(2*Real.sinh (y/2)) : ℝ) : ℂ)*(1-tvKernel e y)) =
      (((∫ y in Ioi (0:ℝ), tvArchIntegrand e y) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [mem_Ioi] at hy
  simp only [tvKernel, abs_of_pos hy, tvArchIntegrand, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem tvTransform_re_zero {e : ℝ} (he : 0 < e) : (tvTransform e 0).re = 2/e := by
  have h := tvTransform_re_mul_I he 0
  simp only [Complex.ofReal_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  rw [h]
  field_simp

theorem tvTransform_re_one {e : ℝ} (he : 0 < e) : (tvTransform e 1).re = 2/e := by
  have h := tvTransform_re_one_add_mul_I he 0
  simp only [Complex.ofReal_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  rw [h]
  field_simp

/-- The finite-field inequality for actual prime ideals in every totally
complex number field. All analytic conditions are discharged by the kernel. -/
theorem tv_primeSide_bound (hcomplex : InfinitePlace.nrRealPlaces K = 0)
    {e a : ℝ} (he : 0 < e) (ha : 0 < a) (ha' : a ≤ 1/4) (hae : a < e) :
    2*(DedekindResidue.primeSideH K a (tvKernel e) 0).re ≤
      Real.log |NumberField.discr K| + (Module.finrank ℚ K : ℝ)*
        (-(Real.eulerMascheroniConstant+Real.log (8*Real.pi)) +
          ∫ y in Ioi (0:ℝ), tvArchIntegrand e y) + 4/e := by
  have h := tvWeilRhs_re_nonneg K he ha ha' hae
  have hdeg : (2:ℝ)*(InfinitePlace.nrComplexPlaces K : ℝ) = (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (show 2*InfinitePlace.nrComplexPlaces K = Module.finrank ℚ K by
      simpa only [hcomplex, zero_add] using InfinitePlace.card_add_two_mul_card_eq_rank K)
  rw [tvWeilRhs, tvKernel_arch_integral] at h
  simp only [hcomplex, Nat.cast_zero, zero_add, zero_mul, mul_zero, add_zero,
    Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, Complex.ofReal_im,
    sub_zero, Nat.cast_mul, Nat.cast_ofNat] at h
  norm_num at h
  rw [tvTransform_re_zero he, tvTransform_re_one he, hdeg] at h
  rw [Real.log_abs]
  convert h using 1 <;> ring

end UnitDistance.NumberFieldAnalysis
