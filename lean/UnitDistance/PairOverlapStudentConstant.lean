module

public import UnitDistance.PairOverlapHyperbola
public import UnitDistance.Upstream.AINTLIB.ExplicitFormula.GammaSide
public import UnitDistance.PairOverlapStudentCompactArithmeticRun20260920

@[expose] public section
set_option backward.privateInPublic true


/-!
# The one transcendental constant in the pair-overlap certificate

All digamma values in the collected overlap reduce to the single constant
`C_s`.  This file rewrites it as a positive elementary integral.  The form
below is suitable for a finite geometric-series certificate with a rational
tail bound.
-/

noncomputable section

open MeasureTheory Set

namespace UnitDistance.Witness

def pairOverlapStudentConstant : ℝ :=
  -2 * (Complex.digamma (s : ℂ)).re +
    (Complex.digamma ((2 * s : ℝ) : ℂ)).re +
    1 / (2 * s - 1) - Real.eulerMascheroniConstant

def pairOverlapStudentKernel (x u : ℝ) : ℝ :=
  Real.exp (-u) * (1 - Real.exp (-(x * u))) ^ 2 /
    (1 - Real.exp (-u))

private theorem complex_digamma_kernel_eq_real (y u : ℝ) :
    (Complex.exp (-(1:ℂ) * (u:ℂ)) - Complex.exp (-(y:ℂ) * (u:ℂ))) /
        (1 - Complex.exp (-(u:ℂ))) =
      (((Real.exp (-u) - Real.exp (-(y*u))) /
        (1 - Real.exp (-u)) : ℝ) : ℂ) := by
  rw [show -(1:ℂ) * (u:ℂ) = ((-u : ℝ) : ℂ) by push_cast; ring,
    show -(y:ℂ) * (u:ℂ) = ((-(y*u) : ℝ) : ℂ) by push_cast; ring,
    show -(u:ℂ) = ((-u : ℝ) : ℂ) by simp]
  rw [← Complex.ofReal_exp]
  norm_cast

private theorem complex_digamma_kernel_re_eq_real (y u : ℝ) :
    ((Complex.exp (-(1:ℂ) * (u:ℂ)) - Complex.exp (-(y:ℂ) * (u:ℂ))) /
        (1 - Complex.exp (-(u:ℂ)))).re =
      (Real.exp (-u) - Real.exp (-(y*u))) /
        (1 - Real.exp (-u)) := by
  calc
    ((Complex.exp (-(1:ℂ) * (u:ℂ)) - Complex.exp (-(y:ℂ) * (u:ℂ))) /
        (1 - Complex.exp (-(u:ℂ)))).re =
        ((((Real.exp (-u) - Real.exp (-(y*u))) /
          (1 - Real.exp (-u)) : ℝ) : ℂ)).re :=
      congrArg Complex.re (complex_digamma_kernel_eq_real y u)
    _ = _ := Complex.ofReal_re _

private theorem digamma_real_sub_one_eq_integral {y : ℝ} (hy : 0 < y) :
    (Complex.digamma (y : ℂ)).re - (Complex.digamma (1 : ℂ)).re =
      ∫ u in Ioi (0 : ℝ),
        (Real.exp (-u) - Real.exp (-(y * u))) /
          (1 - Real.exp (-u)) := by
  have h := DedekindResidue.digamma_sub_digamma_eq_integral
    (σ := (1 : ℝ)) one_pos (w := (y : ℂ)) (by simpa using hy)
  have hI := DedekindResidue.integrableOn_digamma_diff_kernel
    (σ := (1 : ℝ)) one_pos (w := (y : ℂ)) (by simpa using hy)
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re] at hre
  calc
    (Complex.digamma (y : ℂ)).re - (Complex.digamma (1 : ℂ)).re =
        (∫ u in Ioi (0 : ℝ),
          (Complex.exp (-(1:ℂ) * (u:ℂ)) - Complex.exp (-(y:ℂ) * (u:ℂ))) /
            (1 - Complex.exp (-(u:ℂ)))).re := hre
    _ = ∫ u in Ioi (0 : ℝ),
          ((Complex.exp (-(1:ℂ) * (u:ℂ)) - Complex.exp (-(y:ℂ) * (u:ℂ))) /
            (1 - Complex.exp (-(u:ℂ)))).re := (integral_re hI).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact complex_digamma_kernel_re_eq_real y u

theorem pairOverlapStudentConstant_eq_integral :
    pairOverlapStudentConstant =
      2 / (2 * s - 1) -
        ∫ u in Ioi (0 : ℝ), pairOverlapStudentKernel (s - 1) u := by
  have hs : 0 < s := by norm_num [s]
  have heta : 0 < 2 * s - 1 := by norm_num [s]
  have hrec := Complex.digamma_apply_add_one (((2 * s - 1 : ℝ) : ℂ)) (by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num [s] at hre
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith)
  have hrecRe := congrArg Complex.re hrec
  have htwo : (((2 * s - 1 : ℝ) : ℂ) + 1) = ((2 * s : ℝ) : ℂ) := by
    push_cast
    ring
  rw [htwo] at hrecRe
  simp only [Complex.add_re, Complex.inv_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.normSq_apply, add_zero, mul_zero] at hrecRe
  have hrecRe' :
      (Complex.digamma ((2 * s : ℝ) : ℂ)).re =
        (Complex.digamma ((2 * s - 1 : ℝ) : ℂ)).re + 1 / (2*s-1) := by
    rw [hrecRe]
    congr 1
    field_simp [ne_of_gt heta]
  have hpsi1 : (Complex.digamma (1 : ℂ)).re = -Real.eulerMascheroniConstant := by
    rw [Complex.digamma_one]
    simp
  have hsInt := digamma_real_sub_one_eq_integral hs
  have hetaInt := digamma_real_sub_one_eq_integral heta
  unfold pairOverlapStudentConstant
  rw [hrecRe']
  have hcombine :
      (∫ u in Ioi (0 : ℝ),
          (Real.exp (-u) - Real.exp (-((2*s-1) * u))) /
            (1 - Real.exp (-u)))
        - 2 * (∫ u in Ioi (0 : ℝ),
          (Real.exp (-u) - Real.exp (-(s * u))) /
            (1 - Real.exp (-u))) =
      -(∫ u in Ioi (0 : ℝ), pairOverlapStudentKernel (s - 1) u) := by
    rw [← integral_const_mul]
    rw [← integral_sub]
    rw [← integral_neg]
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [Set.mem_Ioi] at hu
      unfold pairOverlapStudentKernel
      have hden : 1 - Real.exp (-u) ≠ 0 := by
        have he := Real.exp_lt_one_iff.mpr (by linarith : -u < 0)
        linarith
      have hexp1 : Real.exp (-(s * u)) =
          Real.exp (-u) * Real.exp (-((s-1)*u)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hexp2 : Real.exp (-((2*s-1) * u)) =
          Real.exp (-u) * Real.exp (-((2*(s-1))*u)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp1, hexp2, show -((2*(s-1))*u) =
        -((s-1)*u) + -((s-1)*u) by ring, Real.exp_add]
      field_simp [hden]
      ring
    · refine (DedekindResidue.integrableOn_digamma_diff_kernel
          (σ := (1 : ℝ)) one_pos (w := (((2*s-1 : ℝ)) : ℂ))
          (by simpa using heta)).re.congr ?_
      filter_upwards with u
      exact complex_digamma_kernel_re_eq_real (2*s-1) u
    · refine ((DedekindResidue.integrableOn_digamma_diff_kernel
          (σ := (1 : ℝ)) one_pos (w := ((s : ℝ) : ℂ))
          (by simpa using hs)).re.const_mul 2).congr ?_
      filter_upwards with u
      simpa using congrArg (fun x : ℝ => 2*x)
        (complex_digamma_kernel_re_eq_real s u)
  have hgamma : Real.eulerMascheroniConstant =
      -(Complex.digamma (1 : ℂ)).re := by linarith [hpsi1]
  rw [hgamma]
  linear_combination hcombine + hetaInt - 2 * hsInt

def pairOverlapStudentSeriesIntegrand (x : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-((n + 1 : ℕ) * u)) * (1 - Real.exp (-(x*u))) ^ 2

def pairOverlapStudentSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  2 * x^2 /
    ((n+1 : ℝ) * (n+1+x) * (n+1+2*x))

def pairOverlapStudentRemainder (x : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-((N+1 : ℕ) * u)) * (1 - Real.exp (-(x*u))) ^ 2 /
    (1 - Real.exp (-u))

private theorem geometric_split (q : ℝ) (hq : 1 - q ≠ 0) (N : ℕ) :
    q / (1-q) = (∑ n ∈ Finset.range N, q^(n+1)) + q^(N+1)/(1-q) := by
  rw [div_eq_iff hq, add_mul, div_mul_cancel₀ _ hq]
  rw [Finset.sum_mul]
  simp_rw [pow_succ]
  simp_rw [show ∀ n : ℕ, q ^ n * q * (1-q) = q * (q^n * (1-q)) by
    intro n; ring]
  rw [← Finset.mul_sum]
  rw [show (∑ n ∈ Finset.range N, q ^ n * (1 - q)) =
      (∑ n ∈ Finset.range N, q ^ n) * (1-q) by rw [Finset.sum_mul]]
  rw [geom_sum_mul_neg]
  ring

theorem pairOverlapStudentKernel_eq_sum_add_remainder
    {x u : ℝ} (hu : 0 < u) (N : ℕ) :
    pairOverlapStudentKernel x u =
      (∑ n ∈ Finset.range N, pairOverlapStudentSeriesIntegrand x n u) +
        pairOverlapStudentRemainder x N u := by
  have hden : 1 - Real.exp (-u) ≠ 0 := by
    have he := Real.exp_lt_one_iff.mpr (by linarith : -u < 0)
    linarith
  have hpow (n : ℕ) : Real.exp (-u) ^ (n+1) =
      Real.exp (-((n+1 : ℕ) * u)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold pairOverlapStudentKernel pairOverlapStudentSeriesIntegrand
    pairOverlapStudentRemainder
  rw [show Real.exp (-u) * (1 - Real.exp (-(x*u))) ^ 2 /
      (1 - Real.exp (-u)) =
      (Real.exp (-u) / (1 - Real.exp (-u))) *
        (1 - Real.exp (-(x*u))) ^ 2 by ring]
  rw [geometric_split (Real.exp (-u)) hden N]
  rw [add_mul, Finset.sum_mul]
  simp_rw [hpow]
  ring

private theorem pairOverlapStudentSeriesIntegrand_eq
    (x : ℝ) (n : ℕ) (u : ℝ) :
    pairOverlapStudentSeriesIntegrand x n u =
      Real.exp (-(n+1 : ℝ)*u) -
        2*Real.exp (-(n+1+x)*u) +
          Real.exp (-(n+1+2*x)*u) := by
  unfold pairOverlapStudentSeriesIntegrand
  rw [show -((n + 1 : ℕ) * u) = -(n+1 : ℝ)*u by norm_num; ring]
  rw [show -(n+1+x)*u = (-(n+1 : ℝ)*u) + -(x*u) by ring,
    show -(n+1+2*x)*u = (-(n+1 : ℝ)*u) + (-(x*u) + -(x*u)) by ring,
    Real.exp_add, Real.exp_add, Real.exp_add]
  ring

theorem integrableOn_pairOverlapStudentSeriesIntegrand
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    IntegrableOn (pairOverlapStudentSeriesIntegrand x n) (Ioi 0) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hnx : (0 : ℝ) < n + 1 + x := by positivity
  have hn2x : (0 : ℝ) < n + 1 + 2*x := by positivity
  have h0 := exp_neg_integrableOn_Ioi 0 hn
  have h1 := exp_neg_integrableOn_Ioi 0 hnx
  have h2 := exp_neg_integrableOn_Ioi 0 hn2x
  have hcomb := (h0.sub (h1.const_mul 2)).add h2
  apply hcomb.congr_fun
  intro u hu
  exact (pairOverlapStudentSeriesIntegrand_eq x n u).symm
  exact measurableSet_Ioi

theorem integral_pairOverlapStudentSeriesIntegrand
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (∫ u in Ioi (0 : ℝ), pairOverlapStudentSeriesIntegrand x n u) =
      pairOverlapStudentSeriesTerm x n := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hnx : (0 : ℝ) < n + 1 + x := by positivity
  have hn2x : (0 : ℝ) < n + 1 + 2*x := by positivity
  have h0 := exp_neg_integrableOn_Ioi 0 hn
  have h1 := exp_neg_integrableOn_Ioi 0 hnx
  have h2 := exp_neg_integrableOn_Ioi 0 hn2x
  calc
    (∫ u in Ioi (0 : ℝ), pairOverlapStudentSeriesIntegrand x n u) =
        ∫ u in Ioi (0 : ℝ),
          Real.exp (-(n+1 : ℝ)*u) -
            2*Real.exp (-(n+1+x)*u) +
              Real.exp (-(n+1+2*x)*u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact pairOverlapStudentSeriesIntegrand_eq x n u
    _ = 1/(n+1 : ℝ) - 2*(1/(n+1+x)) + 1/(n+1+2*x) := by
      have ha := integral_add (μ := volume.restrict (Ioi (0 : ℝ)))
        (h0.sub (h1.const_mul 2)) h2
      have hb := integral_sub (μ := volume.restrict (Ioi (0 : ℝ)))
        h0 (h1.const_mul 2)
      have hi0 : (∫ u in Ioi (0 : ℝ), Real.exp (-(n+1 : ℝ)*u)) =
          1/(n+1 : ℝ) := by
        convert DedekindResidue.integral_exp_neg_mul_Ioi hn using 1 <;> ring
      have hi1 : (∫ u in Ioi (0 : ℝ), Real.exp (-(n+1+x)*u)) =
          1/(n+1+x) := by
        convert DedekindResidue.integral_exp_neg_mul_Ioi hnx using 1 <;> ring
      have hi2 : (∫ u in Ioi (0 : ℝ), Real.exp (-(n+1+2*x)*u)) =
          1/(n+1+2*x) := by
        convert DedekindResidue.integral_exp_neg_mul_Ioi hn2x using 1 <;> ring
      simp only [Pi.add_apply, Pi.sub_apply] at ha hb
      rw [ha, hb, integral_const_mul,
        hi0, hi1, hi2]
    _ = pairOverlapStudentSeriesTerm x n := by
      unfold pairOverlapStudentSeriesTerm
      field_simp [ne_of_gt hn, ne_of_gt hnx, ne_of_gt hn2x]
      ring

theorem pairOverlapStudentRemainder_nonneg
    {x u : ℝ} (hx : 0 ≤ x) (hu : 0 < u) (N : ℕ) :
    0 ≤ pairOverlapStudentRemainder x N u := by
  unfold pairOverlapStudentRemainder
  have hden : 0 < 1 - Real.exp (-u) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -u < 0)
    linarith
  positivity

theorem pairOverlapStudentRemainder_le
    {x u : ℝ} (hx : 0 ≤ x) (hu : 0 < u) {N : ℕ} (hN : 0 < N) :
    pairOverlapStudentRemainder x N u ≤
      x^2 * u * Real.exp (-((N : ℝ)*u)) := by
  have hxu : 0 ≤ x*u := mul_nonneg hx hu.le
  have hone : 0 ≤ 1 - Real.exp (-(x*u)) := by
    have he := Real.exp_le_one_iff.mpr (by linarith : -(x*u) ≤ 0)
    linarith
  have hlin : 1 - Real.exp (-(x*u)) ≤ x*u := by
    have he := Real.add_one_le_exp (-(x*u))
    linarith
  have hsq : (1 - Real.exp (-(x*u)))^2 ≤ (x*u)^2 := by
    nlinarith [sq_nonneg ((x*u) - (1 - Real.exp (-(x*u))))]
  have hden : 0 < 1 - Real.exp (-u) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -u < 0)
    linarith
  have hdenlower : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by
    have he := Real.add_one_le_exp u
    have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-u)).le
    have hcancel : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hcancel] at hm
    linarith
  rw [show pairOverlapStudentRemainder x N u =
      Real.exp (-(((N:ℝ)+1)*u)) * (1 - Real.exp (-(x*u)))^2 /
        (1 - Real.exp (-u)) by
    unfold pairOverlapStudentRemainder
    norm_num]
  rw [div_le_iff₀ hden]
  calc
    Real.exp (-(((N:ℝ)+1)*u)) * (1 - Real.exp (-(x*u)))^2 ≤
        Real.exp (-(((N:ℝ)+1)*u)) * (x*u)^2 :=
      mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = (x^2*u*Real.exp (-((N:ℝ)*u))) * (u*Real.exp (-u)) := by
      rw [show -(((N:ℝ)+1)*u) = -((N:ℝ)*u) + -u by ring,
        Real.exp_add]
      ring
    _ ≤ (x^2*u*Real.exp (-((N:ℝ)*u))) * (1 - Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left hdenlower (by positivity)

theorem integrableOn_pairOverlapStudentRemainder
    {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : 0 < N) :
    IntegrableOn (pairOverlapStudentRemainder x N) (Ioi 0) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hbase := Real.GammaIntegral_convergent (show (0 : ℝ) < 2 by norm_num)
  have hscaled : IntegrableOn
      (fun u : ℝ => Real.exp (-(N*u)) * (N*u)^(2-1 : ℝ)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun y : ℝ => Real.exp (-y) * y^(2-1 : ℝ)) 0 hNr).2
    simpa using hbase
  have hscale : IntegrableOn
      (fun u : ℝ => x^2 / N *
        (Real.exp (-(N*u)) * (N*u)^(2-1 : ℝ))) (Ioi 0) :=
    hscaled.const_mul (x^2/N)
  have hdom : IntegrableOn
      (fun u : ℝ => x^2*u*Real.exp (-((N:ℝ)*u))) (Ioi 0) := by
    apply hscale.congr_fun
    · intro u hu
      simp only [show (2-1 : ℝ) = 1 by norm_num, Real.rpow_one]
      field_simp [ne_of_gt hNr]
    · exact measurableSet_Ioi
  apply hdom.mono'
  · unfold pairOverlapStudentRemainder
    refine (ContinuousOn.div (by fun_prop) (by fun_prop) ?_).aestronglyMeasurable
      measurableSet_Ioi
    intro u hu
    have hu' : 0 < u := hu
    have he := Real.exp_lt_one_iff.mpr (by linarith : -u < 0)
    linarith
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pairOverlapStudentRemainder_nonneg hx hu N)]
    exact pairOverlapStudentRemainder_le hx hu hN

theorem integral_pairOverlapStudentRemainder_le
    {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : 0 < N) :
    (∫ u in Ioi (0 : ℝ), pairOverlapStudentRemainder x N u) ≤
      x^2 / N^2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdom : IntegrableOn
      (fun u : ℝ => x^2*u*Real.exp (-((N:ℝ)*u))) (Ioi 0) := by
    have hbase := Real.GammaIntegral_convergent (show (0 : ℝ) < 2 by norm_num)
    have hscaled : IntegrableOn
        (fun u : ℝ => Real.exp (-(N*u)) * (N*u)^(2-1 : ℝ)) (Ioi 0) := by
      apply (integrableOn_Ioi_comp_mul_left_iff
        (fun y : ℝ => Real.exp (-y) * y^(2-1 : ℝ)) 0 hNr).2
      simpa using hbase
    have hscale : IntegrableOn
        (fun u : ℝ => x^2/N *
          (Real.exp (-(N*u)) * (N*u)^(2-1 : ℝ))) (Ioi 0) :=
      hscaled.const_mul (x^2/N)
    apply hscale.congr_fun
    · intro u hu
      simp only [show (2-1 : ℝ) = 1 by norm_num, Real.rpow_one]
      field_simp [ne_of_gt hNr]
    · exact measurableSet_Ioi
  calc
    (∫ u in Ioi (0 : ℝ), pairOverlapStudentRemainder x N u) ≤
        ∫ u in Ioi (0 : ℝ), x^2*u*Real.exp (-((N:ℝ)*u)) := by
      apply integral_mono_ae (integrableOn_pairOverlapStudentRemainder hx hN) hdom
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      exact pairOverlapStudentRemainder_le hx hu hN
    _ = x^2 * ((1/(N:ℝ))^2 * Real.Gamma 2) := by
      have hinner : (∫ u in Ioi (0 : ℝ),
          u*Real.exp (-((N:ℝ)*u))) =
          (1/(N:ℝ))^2 * Real.Gamma 2 := by
        rw [show (fun u : ℝ => u*Real.exp (-((N:ℝ)*u))) =
            (fun u : ℝ => u^(2-1 : ℝ)*Real.exp (-((N:ℝ)*u))) by
          funext u
          rw [show (2-1 : ℝ) = 1 by norm_num, Real.rpow_one]]
        rw [Real.integral_rpow_mul_exp_neg_mul_Ioi
          (a := (2:ℝ)) (r := (N:ℝ)) (by norm_num) hNr,
          Real.rpow_two]
      rw [show (fun u : ℝ => x^2*u*Real.exp (-((N:ℝ)*u))) =
          (fun u : ℝ => x^2 * (u*Real.exp (-((N:ℝ)*u)))) by
        funext u; ring,
        integral_const_mul, hinner]
    _ = x^2 / N^2 := by
      rw [Real.Gamma_two]
      field_simp [ne_of_gt hNr]

theorem pairOverlapStudentIntegral_le_finite
    {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : 0 < N) :
    (∫ u in Ioi (0 : ℝ), pairOverlapStudentKernel x u) ≤
      (∑ n ∈ Finset.range N, pairOverlapStudentSeriesTerm x n) + x^2/N^2 := by
  have hsum : IntegrableOn
      (fun u : ℝ => ∑ n ∈ Finset.range N,
        pairOverlapStudentSeriesIntegrand x n u) (Ioi 0) :=
    integrable_finsetSum (Finset.range N) (fun n hn =>
      integrableOn_pairOverlapStudentSeriesIntegrand hx n)
  have hrem := integrableOn_pairOverlapStudentRemainder hx hN
  have heq : (∫ u in Ioi (0 : ℝ), pairOverlapStudentKernel x u) =
      (∫ u in Ioi (0 : ℝ),
        (∑ n ∈ Finset.range N, pairOverlapStudentSeriesIntegrand x n u) +
          pairOverlapStudentRemainder x N u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact pairOverlapStudentKernel_eq_sum_add_remainder hu N
  rw [heq, integral_add hsum hrem]
  have hprefix :
      (∫ u in Ioi (0 : ℝ), ∑ n ∈ Finset.range N,
        pairOverlapStudentSeriesIntegrand x n u) =
        ∑ n ∈ Finset.range N, pairOverlapStudentSeriesTerm x n := by
    rw [integral_finsetSum (Finset.range N) (fun n hn =>
      integrableOn_pairOverlapStudentSeriesIntegrand hx n)]
    apply Finset.sum_congr rfl
    intro n hn
    exact integral_pairOverlapStudentSeriesIntegrand hx n
  rw [hprefix]
  linarith [integral_pairOverlapStudentRemainder_le hx hN]

theorem pairOverlapStudentConstant_lower_finite {N : ℕ} (hN : 0 < N) :
    2 / (2*s-1) -
        ((∑ n ∈ Finset.range N, pairOverlapStudentSeriesTerm (s-1) n) +
          (s-1)^2/N^2) ≤ pairOverlapStudentConstant := by
  rw [pairOverlapStudentConstant_eq_integral]
  have hs0 : (0 : ℝ) ≤ s-1 := by norm_num [s]
  linarith [pairOverlapStudentIntegral_le_finite hs0 hN]

/-- A rational lower endpoint for the sole digamma constant in the witness.
The proof evaluates 3500 positive geometric terms and uses the explicit
`x²/N²` bound for the remaining tail. -/
theorem pairOverlapStudentConstant_lower :
    (1511896398840 : ℝ) / 1000000000000 ≤ pairOverlapStudentConstant := by
  rw [show (1000000000000 : ℝ) = 10 ^ 12 by norm_num]
  apply PairOverlapStudentCompactArithmeticRun20260920.finite_expression_lower.trans
  simpa only [PairOverlapStudentCompactArithmeticRun20260920.sigma,
    PairOverlapStudentCompactArithmeticRun20260920.seriesTerm,
    PairOverlapStudentCompactArithmeticRun20260920.termCount,
    s, pairOverlapStudentSeriesTerm] using
      pairOverlapStudentConstant_lower_finite (N := 3500) (by norm_num)

end UnitDistance.Witness
