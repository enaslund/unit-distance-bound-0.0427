module

public import UnitDistance.PairOverlapHyperbolaRemainder
public import UnitDistance.Upstream.AINTLIB.ExplicitFormula.GammaSide

@[expose] public section
set_option backward.privateInPublic true


/-! Evaluation of the elementary leading hyperbola integral. -/

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnitDistance

def pairHyperbolaGaussDifference (A x : ℝ) : ℝ :=
  ((1+x)^(-A) - (1+x)^(-(1:ℝ))) / x

def pairHyperbolaBoundaryDifference (A x : ℝ) : ℝ :=
  (1 + Real.exp x)^(-A) - (1 + Real.exp x)^(-(1:ℝ))

private theorem cpow_neg_ofReal_eq_rpow (A : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ((x : ℝ) : ℂ) ^ (-((A : ℝ) : ℂ)) = (((x ^ (-A) : ℝ) : ℂ)) := by
  simpa only [Complex.ofReal_neg] using (Complex.ofReal_cpow hx (-A)).symm

private theorem gauss_complex_difference_eq_real (A : ℝ) {x : ℝ}
    (hx : 0 < x) :
    ((((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-(1:ℂ))) / (x:ℂ) -
      (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-((A:ℝ):ℂ))) /
        (x:ℂ)) = ((pairHyperbolaGaussDifference A x : ℝ) : ℂ) := by
  have hpow1 : ((1+x : ℝ) : ℂ) ^ (-(1:ℂ)) =
      ((((1+x)^(-(1:ℝ))) : ℝ) : ℂ) := by
    simpa using cpow_neg_ofReal_eq_rpow 1 (by positivity : 0 ≤ 1+x)
  have hpowA := cpow_neg_ofReal_eq_rpow A (by positivity : 0 ≤ 1+x)
  rw [hpow1, hpowA]
  unfold pairHyperbolaGaussDifference
  push_cast
  field_simp [hx.ne']
  ring

theorem integrableOn_pairHyperbolaGaussDifference {A : ℝ} (hA : 0 < A) :
    IntegrableOn (pairHyperbolaGaussDifference A) (Ioi 0) := by
  have h1 := DedekindResidue.integrableOn_gauss_one_integrand
    (z := (1:ℂ)) (by norm_num)
  have hA' := DedekindResidue.integrableOn_gauss_one_integrand
    (z := (A:ℂ)) (by simpa using hA)
  have hc := h1.sub hA'
  apply hc.re.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  rw [Set.mem_Ioi] at hx
  exact congrArg Complex.re (gauss_complex_difference_eq_real A hx)

theorem integral_pairHyperbolaGaussDifference {A : ℝ} (hA : 0 < A) :
    (∫ x in Ioi (0:ℝ), pairHyperbolaGaussDifference A x) =
      (Complex.digamma (1:ℂ)).re - (Complex.digamma (A:ℂ)).re := by
  have h1 := DedekindResidue.integrableOn_gauss_one_integrand
    (z := (1:ℂ)) (by norm_num)
  have hA' := DedekindResidue.integrableOn_gauss_one_integrand
    (z := (A:ℂ)) (by simpa using hA)
  have hc := h1.sub hA'
  have hpsi1 := DedekindResidue.digamma_eq_integral_gauss_one
    (z := (1:ℂ)) (by norm_num)
  have hpsiA := DedekindResidue.digamma_eq_integral_gauss_one
    (z := (A:ℂ)) (by simpa using hA)
  have hcomplex : Complex.digamma (1:ℂ) - Complex.digamma (A:ℂ) =
      ∫ x in Ioi (0:ℝ),
        ((((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-(1:ℂ))) / (x:ℂ) -
          (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-((A:ℝ):ℂ))) /
            (x:ℂ)) := by
    rw [hpsi1, hpsiA, integral_sub h1 hA']
  calc
    (∫ x in Ioi (0:ℝ), pairHyperbolaGaussDifference A x) =
        ∫ x in Ioi (0:ℝ),
          (((((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-(1:ℂ))) / (x:ℂ) -
            (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-((A:ℝ):ℂ))) /
              (x:ℂ))).re := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        rw [Set.mem_Ioi] at hx
        exact (congrArg Complex.re (gauss_complex_difference_eq_real A hx)).symm
    _ = (∫ x in Ioi (0:ℝ),
          ((((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-(1:ℂ))) / (x:ℂ) -
            (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-((A:ℝ):ℂ))) /
              (x:ℂ))).re := integral_re hc
    _ = (Complex.digamma (1:ℂ) - Complex.digamma (A:ℂ)).re :=
      congrArg Complex.re hcomplex.symm
    _ = _ := by simp

private theorem exp_image_univ : Real.exp '' (Set.univ : Set ℝ) = Ioi 0 := by
  rw [image_univ, Real.range_exp]

private theorem exp_gauss_transform (A x : ℝ) :
    |Real.exp x| * pairHyperbolaGaussDifference A (Real.exp x) =
      pairHyperbolaBoundaryDifference A x := by
  rw [abs_of_pos (Real.exp_pos x)]
  unfold pairHyperbolaGaussDifference pairHyperbolaBoundaryDifference
  field_simp [Real.exp_ne_zero x]

theorem integrable_pairHyperbolaBoundaryDifference {A : ℝ} (hA : 0 < A) :
    Integrable (pairHyperbolaBoundaryDifference A) := by
  have hchange := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := (Set.univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (pairHyperbolaGaussDifference A)
  rw [exp_image_univ] at hchange
  have ht := hchange.mp (integrableOn_pairHyperbolaGaussDifference hA)
  rw [integrableOn_univ] at ht
  apply ht.congr
  filter_upwards with x
  simpa only [smul_eq_mul] using exp_gauss_transform A x

theorem integral_pairHyperbolaBoundaryDifference {A : ℝ} (hA : 0 < A) :
    (∫ x : ℝ, pairHyperbolaBoundaryDifference A x) =
      (Complex.digamma (1:ℂ)).re - (Complex.digamma (A:ℂ)).re := by
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := (Set.univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (pairHyperbolaGaussDifference A)
  rw [exp_image_univ] at hchange
  simp only [Measure.restrict_univ] at hchange
  rw [← integral_pairHyperbolaGaussDifference hA, hchange]
  apply integral_congr_ae
  filter_upwards with x
  simpa only [smul_eq_mul] using (exp_gauss_transform A x).symm

def pairHyperbolaBaseAntiderivative (b u : ℝ) : ℝ :=
  u - Real.log (1 + b*Real.exp (2*u))/2 +
    Real.log (1 + b*Real.exp (-2*u))/2

private theorem hasDerivAt_pairHyperbolaBaseAntiderivative {b : ℝ}
    (hb : 0 < b) (u : ℝ) :
    HasDerivAt (pairHyperbolaBaseAntiderivative b)
      (pairHyperbolaLeadingIntegrand 1 1 b u) u := by
  have hp : 0 < 1 + b*Real.exp (2*u) := by positivity
  have hn : 0 < 1 + b*Real.exp (-2*u) := by positivity
  have hep : HasDerivAt (fun u : ℝ => 1 + b*Real.exp (2*u))
      (b*(Real.exp (2*u)*2)) u := by
    have hlin : HasDerivAt (fun u : ℝ => 2*u) 2 u := hasDerivAt_const_mul 2
    have he := (Real.hasDerivAt_exp (2*u)).comp u hlin
    simpa only [Function.comp_apply] using (he.const_mul b).const_add 1
  have hen : HasDerivAt (fun u : ℝ => 1 + b*Real.exp (-2*u))
      (b*(Real.exp (-2*u)*(-2))) u := by
    have hlin : HasDerivAt (fun u : ℝ => (-2)*u) (-2) u :=
      hasDerivAt_const_mul (-2)
    have he := (Real.hasDerivAt_exp (-2*u)).comp u hlin
    simpa only [Function.comp_apply] using (he.const_mul b).const_add 1
  have hlogp := (Real.hasDerivAt_log hp.ne').comp u hep
  have hlogn := (Real.hasDerivAt_log hn.ne').comp u hen
  have hderiv := ((hasDerivAt_id u).sub (hlogp.div_const 2)).add (hlogn.div_const 2)
  apply hderiv.congr_deriv
  unfold pairHyperbolaLeadingIntegrand pairHyperbolaFirstFactor
    pairHyperbolaSecondFactor
  rw [Real.rpow_neg_one, Real.rpow_neg_one]
  field_simp [hp.ne', hn.ne']
  ring

private theorem pairHyperbolaBaseAntiderivative_eq_top {b : ℝ}
    (hb : 0 < b) (u : ℝ) :
    pairHyperbolaBaseAntiderivative b u =
      -Real.log b/2 - Real.log (1 + Real.exp (-2*u)/b)/2 +
        Real.log (1 + b*Real.exp (-2*u))/2 := by
  have he : 0 < Real.exp (2*u) := Real.exp_pos _
  have hbe : 0 < b*Real.exp (2*u) := mul_pos hb he
  have hexpinv : Real.exp (-2*u) = (Real.exp (2*u))⁻¹ := by
    rw [show -2*u = -(2*u) by ring, Real.exp_neg]
  have hfactor : 1 + b*Real.exp (2*u) =
      (b*Real.exp (2*u)) * (1 + Real.exp (-2*u)/b) := by
    rw [hexpinv]
    field_simp [hb.ne', he.ne']
    ring
  unfold pairHyperbolaBaseAntiderivative
  rw [hfactor, Real.log_mul hbe.ne' (by positivity), Real.log_mul hb.ne' he.ne',
    Real.log_exp]
  ring

private theorem pairHyperbolaBaseAntiderivative_eq_bot {b : ℝ}
    (hb : 0 < b) (u : ℝ) :
    pairHyperbolaBaseAntiderivative b u =
      Real.log b/2 - Real.log (1 + b*Real.exp (2*u))/2 +
        Real.log (1 + Real.exp (2*u)/b)/2 := by
  have he : 0 < Real.exp (-2*u) := Real.exp_pos _
  have hbe : 0 < b*Real.exp (-2*u) := mul_pos hb he
  have hfactor : 1 + b*Real.exp (-2*u) =
      (b*Real.exp (-2*u)) * (1 + Real.exp (2*u)/b) := by
    rw [show Real.exp (2*u) = (Real.exp (-2*u))⁻¹ by
      rw [← Real.exp_neg]; congr 1; ring]
    field_simp [hb.ne', he.ne']
    ring
  unfold pairHyperbolaBaseAntiderivative
  rw [hfactor, Real.log_mul hbe.ne' (by positivity), Real.log_mul hb.ne' he.ne',
    Real.log_exp]
  ring

private theorem tendsto_exp_two_mul_atBot :
    Tendsto (fun u : ℝ => Real.exp (2*u)) atBot (nhds 0) := by
  have hmul : Tendsto (fun u : ℝ => 2*u) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (show (0:ℝ) < 2 by norm_num)).2 tendsto_id
  exact Real.tendsto_exp_atBot.comp hmul

private theorem tendsto_exp_neg_two_mul_atTop :
    Tendsto (fun u : ℝ => Real.exp (-2*u)) atTop (nhds 0) := by
  have hmul : Tendsto (fun u : ℝ => 2*u) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (show (0:ℝ) < 2 by norm_num)).2 tendsto_id
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul using 1
  funext u
  simp only [Function.comp_apply]
  congr 1
  ring

private theorem tendsto_pairHyperbolaBaseAntiderivative_atTop {b : ℝ}
    (hb : 0 < b) :
    Tendsto (pairHyperbolaBaseAntiderivative b) atTop (nhds (-Real.log b/2)) := by
  have he := tendsto_exp_neg_two_mul_atTop
  have hone : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hfirst : Tendsto (fun u : ℝ => Real.log (1 + Real.exp (-2*u)/b))
      atTop (nhds 0) := by
    convert (((hone.add (he.div_const b)).log (by norm_num))) using 1 <;>
      norm_num
  have hsecond : Tendsto (fun u : ℝ => Real.log (1 + b*Real.exp (-2*u)))
      atTop (nhds 0) := by
    convert (((hone.add (he.const_mul b)).log (by norm_num))) using 1 <;>
      norm_num
  rw [show pairHyperbolaBaseAntiderivative b = fun u =>
      -Real.log b/2 - Real.log (1 + Real.exp (-2*u)/b)/2 +
        Real.log (1 + b*Real.exp (-2*u))/2 by
    funext u; exact pairHyperbolaBaseAntiderivative_eq_top hb u]
  convert (tendsto_const_nhds.sub (hfirst.div_const 2)).add
    (hsecond.div_const 2) using 1 <;> ring

private theorem tendsto_pairHyperbolaBaseAntiderivative_atBot {b : ℝ}
    (hb : 0 < b) :
    Tendsto (pairHyperbolaBaseAntiderivative b) atBot (nhds (Real.log b/2)) := by
  have he := tendsto_exp_two_mul_atBot
  have hone : Tendsto (fun _ : ℝ => (1:ℝ)) atBot (nhds 1) := tendsto_const_nhds
  have hfirst : Tendsto (fun u : ℝ => Real.log (1 + b*Real.exp (2*u)))
      atBot (nhds 0) := by
    convert (((hone.add (he.const_mul b)).log (by norm_num))) using 1 <;>
      norm_num
  have hsecond : Tendsto (fun u : ℝ => Real.log (1 + Real.exp (2*u)/b))
      atBot (nhds 0) := by
    convert (((hone.add (he.div_const b)).log (by norm_num))) using 1 <;>
      norm_num
  rw [show pairHyperbolaBaseAntiderivative b = fun u =>
      Real.log b/2 - Real.log (1 + b*Real.exp (2*u))/2 +
        Real.log (1 + Real.exp (2*u)/b)/2 by
    funext u; exact pairHyperbolaBaseAntiderivative_eq_bot hb u]
  convert (tendsto_const_nhds.sub (hfirst.div_const 2)).add
    (hsecond.div_const 2) using 1 <;> ring

theorem integral_pairHyperbolaLeadingIntegrand_one_one {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) :
    (∫ u : ℝ, pairHyperbolaLeadingIntegrand 1 1 b u) = Real.log (1/b) := by
  rw [integral_of_hasDerivAt_of_tendsto
    (hasDerivAt_pairHyperbolaBaseAntiderivative hb)
    (integrable_pairHyperbolaLeadingIntegrand one_pos one_pos hb hb1)
    (tendsto_pairHyperbolaBaseAntiderivative_atBot hb)
    (tendsto_pairHyperbolaBaseAntiderivative_atTop hb)]
  rw [Real.log_div one_ne_zero hb.ne', Real.log_one]
  ring

private theorem pairHyperbolaFirstFactor_sub_one_eq_boundary
    {A b : ℝ} (hb : 0 < b) (u : ℝ) :
    pairHyperbolaFirstFactor A b u - pairHyperbolaFirstFactor 1 b u =
      pairHyperbolaBoundaryDifference A (2*u + Real.log b) := by
  have harg : 1 + b*Real.exp (2*u) =
      1 + Real.exp (2*u + Real.log b) := by
    rw [Real.exp_add, Real.exp_log hb]
    ring
  unfold pairHyperbolaFirstFactor pairHyperbolaBoundaryDifference
  rw [harg]

private theorem pairHyperbolaSecondFactor_sub_one_eq_boundary
    {B b : ℝ} (hb : 0 < b) (u : ℝ) :
    pairHyperbolaSecondFactor B b u - pairHyperbolaSecondFactor 1 b u =
      pairHyperbolaBoundaryDifference B (-2*u + Real.log b) := by
  have harg : 1 + b*Real.exp (-2*u) =
      1 + Real.exp (-2*u + Real.log b) := by
    rw [Real.exp_add, Real.exp_log hb]
    ring
  unfold pairHyperbolaSecondFactor pairHyperbolaBoundaryDifference
  rw [harg]

private theorem integrable_boundary_two_add_log {A b : ℝ}
    (hA : 0 < A) (hb : 0 < b) :
    Integrable (fun u : ℝ =>
      pairHyperbolaBoundaryDifference A (2*u + Real.log b)) := by
  have hscale : Integrable (fun u : ℝ =>
      pairHyperbolaBoundaryDifference A (2*u)) :=
    (integrable_comp_mul_left_iff (pairHyperbolaBoundaryDifference A)
      (show (2:ℝ) ≠ 0 by norm_num)).2
      (integrable_pairHyperbolaBoundaryDifference hA)
  have hshift := hscale.comp_add_right (Real.log b/2)
  apply hshift.congr
  filter_upwards with u
  congr 2
  ring

private theorem integrable_boundary_neg_two_add_log {A b : ℝ}
    (hA : 0 < A) (hb : 0 < b) :
    Integrable (fun u : ℝ =>
      pairHyperbolaBoundaryDifference A (-2*u + Real.log b)) := by
  have hscale : Integrable (fun u : ℝ =>
      pairHyperbolaBoundaryDifference A ((-2)*u)) :=
    (integrable_comp_mul_left_iff (pairHyperbolaBoundaryDifference A)
      (show (-2:ℝ) ≠ 0 by norm_num)).2
      (integrable_pairHyperbolaBoundaryDifference hA)
  have hshift := hscale.comp_add_right (-Real.log b/2)
  apply hshift.congr
  filter_upwards with u
  congr 2
  ring

private theorem integral_boundary_two_add_log {A b : ℝ}
    (hA : 0 < A) (hb : 0 < b) :
    (∫ u : ℝ, pairHyperbolaBoundaryDifference A (2*u + Real.log b)) =
      ((Complex.digamma (1:ℂ)).re - (Complex.digamma (A:ℂ)).re) / 2 := by
  let f : ℝ → ℝ := fun u => pairHyperbolaBoundaryDifference A (2*u)
  have htranslate := integral_add_right_eq_self
    (μ := (volume : Measure ℝ)) f (Real.log b/2)
  have hscale := Measure.integral_comp_mul_left
    (pairHyperbolaBoundaryDifference A) (2:ℝ)
  calc
    (∫ u : ℝ, pairHyperbolaBoundaryDifference A (2*u + Real.log b)) =
        ∫ u : ℝ, f (u + Real.log b/2) := by
      apply integral_congr_ae
      filter_upwards with u
      unfold f
      congr 2
      ring
    _ = ∫ u : ℝ, f u := htranslate
    _ = |((2:ℝ)⁻¹)| *
        (∫ x : ℝ, pairHyperbolaBoundaryDifference A x) := by
      simpa [f, smul_eq_mul] using hscale
    _ = _ := by
      rw [integral_pairHyperbolaBoundaryDifference hA]
      norm_num
      ring

private theorem integral_boundary_neg_two_add_log {A b : ℝ}
    (hA : 0 < A) (hb : 0 < b) :
    (∫ u : ℝ, pairHyperbolaBoundaryDifference A (-2*u + Real.log b)) =
      ((Complex.digamma (1:ℂ)).re - (Complex.digamma (A:ℂ)).re) / 2 := by
  let f : ℝ → ℝ := fun u => pairHyperbolaBoundaryDifference A ((-2)*u)
  have htranslate := integral_add_right_eq_self
    (μ := (volume : Measure ℝ)) f (-Real.log b/2)
  have hscale := Measure.integral_comp_mul_left
    (pairHyperbolaBoundaryDifference A) (-2:ℝ)
  calc
    (∫ u : ℝ, pairHyperbolaBoundaryDifference A (-2*u + Real.log b)) =
        ∫ u : ℝ, f (u + -Real.log b/2) := by
      apply integral_congr_ae
      filter_upwards with u
      unfold f
      congr 2
      ring
    _ = ∫ u : ℝ, f u := htranslate
    _ = |((-2:ℝ)⁻¹)| *
        (∫ x : ℝ, pairHyperbolaBoundaryDifference A x) := by
      simpa [f, smul_eq_mul] using hscale
    _ = _ := by
      rw [integral_pairHyperbolaBoundaryDifference hA]
      norm_num
      ring

/-- The leading hyperbola integral is exactly its logarithmic/digamma term.
This is the `n = 0` term of the usual zero-balanced hypergeometric expansion,
obtained here without introducing that series. -/
theorem pairHyperbolaLeading_eq_log_digamma {A B b : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hb : 0 < b) (hb1 : b ≤ 1) :
    pairHyperbolaLeading A B b =
      Real.log (1/b) +
        ((Complex.digamma (1:ℂ)).re - (Complex.digamma (A:ℂ)).re)/2 +
        ((Complex.digamma (1:ℂ)).re - (Complex.digamma (B:ℂ)).re)/2 := by
  have hbase := integrable_pairHyperbolaLeadingIntegrand one_pos one_pos hb hb1
  have hcorA := integrable_boundary_two_add_log hA hb
  have hcorB := integrable_boundary_neg_two_add_log hB hb
  unfold pairHyperbolaLeading
  calc
    (∫ u : ℝ, pairHyperbolaLeadingIntegrand A B b u) =
        ∫ u : ℝ, pairHyperbolaLeadingIntegrand 1 1 b u +
          pairHyperbolaBoundaryDifference A (2*u + Real.log b) +
          pairHyperbolaBoundaryDifference B (-2*u + Real.log b) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [← pairHyperbolaFirstFactor_sub_one_eq_boundary hb,
        ← pairHyperbolaSecondFactor_sub_one_eq_boundary hb]
      unfold pairHyperbolaLeadingIntegrand
      ring
    _ = (∫ u : ℝ, pairHyperbolaLeadingIntegrand 1 1 b u +
          pairHyperbolaBoundaryDifference A (2*u + Real.log b)) +
          (∫ u : ℝ, pairHyperbolaBoundaryDifference B
            (-2*u + Real.log b)) :=
      integral_add (hbase.add hcorA) hcorB
    _ = ((∫ u : ℝ, pairHyperbolaLeadingIntegrand 1 1 b u) +
          (∫ u : ℝ, pairHyperbolaBoundaryDifference A
            (2*u + Real.log b))) +
          (∫ u : ℝ, pairHyperbolaBoundaryDifference B
            (-2*u + Real.log b)) := by
      rw [integral_add hbase hcorA]
    _ = _ := by
      rw [integral_pairHyperbolaLeadingIntegrand_one_one hb hb1,
        integral_boundary_two_add_log hA hb,
        integral_boundary_neg_two_add_log hB hb]

theorem pairHyperbola_eq_log_digamma_add_remainder {A B b : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hb : 0 < b) (hb1 : b ≤ 1) :
    pairHyperbola A B b =
      Real.log (1/b) +
        ((Complex.digamma (1:ℂ)).re - (Complex.digamma (A:ℂ)).re)/2 +
        ((Complex.digamma (1:ℂ)).re - (Complex.digamma (B:ℂ)).re)/2 +
        pairHyperbolaRemainder A B b := by
  rw [pairHyperbola_eq_leading_add_remainder hA hB hb hb1,
    pairHyperbolaLeading_eq_log_digamma hA hB hb hb1]

end UnitDistance
